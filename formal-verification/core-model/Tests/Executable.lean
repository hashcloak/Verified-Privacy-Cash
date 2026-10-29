/-
The program model can be run: `step` is computable, so it can be evaluated on
concrete states, instructions and deployments. This file checks that on small
scenarios with a toy deployment (made-up addresses and crypto): `initialize`,
then a SOL deposit through `transact` and its events, and a replay of the same
nullifiers. Conformance tests against the real program (LiteSVM traces) build
on this.
-/
import PrivacyCash
open Aeneas Aeneas.Std PrivacyCash.Model

namespace PrivacyCash.Tests.Executable

/-- The address whose 32 bytes are all `b`. -/
def key (b : Nat) : Pubkey :=
  Std.Array.repeat 32#usize (U8.ofNatCore (b % 256) (by simp only [UScalarTy.numBits]; omega))

/-- 64 zero bytes, and a pairing answer of 1 (big-endian). -/
def zeros64 : Std.Array U8 64#usize := Std.Array.repeat 64#usize 0#u8
def pairingOne : Std.Array U8 32#usize :=
  Std.Array.from (List.replicate 31 0#u8 ++ [1#u8]) (by simp)

/-- A toy deployment. The address derivation is a small hash of the seed
    bytes (the scenarios check that the addresses they use are distinct). The
    crypto accepts: Poseidon returns its left input with non-zero empty-subtree
    roots, SHA-256 returns zeros, and the `alt_bn128` syscalls succeed with a
    pairing product of 1, so any well-formed proof verifies. -/
def deployment : Deployment where
  programId := key 7
  createProgramAddress seeds := key (seeds.foldl (fun acc b => (acc * 37 + b.val) % 251) 7)
  canonicalBump _ := 255#u8
  crypto :=
    { hasher := { hash_pair := fun a _ => .ok a, zero_bytes := .ok (Std.Array.repeat 41#usize (key 5)) }
      sha256 := { hash := fun _ => .ok (key 0) }
      altBn128 := ⟨fun _ => some zeros64, fun _ => some zeros64, fun _ => some pairingOne⟩ }
  adminPubkey := none

/-- Before `initialize`: only the authority (`key 1`) holds lamports. -/
def genesis : State :=
  State.set (fun _ => Account.default) (key 1)
    { lamports := 10000000#u64, owner := systemProgram, data := .empty }

/-- Signed by the authority; rent is 10 lamports per byte. -/
def tx : TxEnv := { signers := [key 1], minimumBalance := some fun n => ⟨BitVec.ofNat 64 (n * 10)⟩ }

def initIx : Instruction := .initialize
  { treeAccount := deployment.pda merkleTreeSeeds, treeTokenAccount := deployment.pda treeTokenSeeds,
    globalConfig := deployment.pda globalConfigSeeds, authority := key 1,
    systemProgram := systemProgram }

def isAccountsError : Except PrivacyCash.Model.Error (State × List CommitmentData) → Bool
  | .error .accounts => true
  | _ => false

-- `initialize` succeeds: the authority pays the three accounts' rent
-- ((4136 + 41 + 48) bytes × 10), and the program owns them.
#guard match step deployment genesis tx initIx with
  | .ok (s, events) => events.isEmpty && (s (key 1)).lamports.val == 10000000 - (4136 + 41 + 48) * 10 &&
      [merkleTreeSeeds, treeTokenSeeds, globalConfigSeeds].all fun seeds =>
        decide ((s (deployment.pda seeds)).owner = deployment.programId)
  | .error _ => false

-- A second `initialize` fails: the accounts already exist.
#guard match step deployment genesis tx initIx with
  | .ok (s, _) => isAccountsError (step deployment s tx initIx)
  | .error _ => false

-- Without the authority's signature, `initialize` fails.
#guard isAccountsError (step deployment genesis { tx with signers := [] } initIx)

/-! ## A SOL deposit -/

/-- The chain after `initialize`. -/
def initialized : State :=
  match step deployment genesis tx initIx with
  | .ok (s, _) => s
  | .error _ => genesis

/-- `x` as 32 big-endian bytes (`x < 256`). -/
def be32 (x : Nat) : Std.Array U8 32#usize :=
  Std.Array.from (List.replicate 31 0#u8 ++ [U8.ofNatCore (x % 256) (by simp only [UScalarTy.numBits]; omega)])
    (by simp)

/-- The generator (1, 2) as a big-endian G1 point (a valid `proof_a`). -/
def generatorBE : Std.Array U8 64#usize :=
  Std.Array.from ((be32 1).val ++ (be32 2).val) (by simp [be32])

/-- A deposit of 200 lamports, no fee, spending nullifiers `key 11` and
    `key 12` and creating commitments `key 21` and `key 22`. The root is the
    empty tree's (`key 5`), the ext-data hash matches the toy SHA-256 (zero). -/
def depositProof : zkcash_core.transact.Proof where
  proof_a := generatorBE
  proof_b := Std.Array.repeat 128#usize 0#u8
  proof_c := zeros64
  root := key 5
  public_amount := be32 200
  ext_data_hash := Std.Array.repeat 32#usize 0#u8
  input_nullifiers := Std.Array.from [key 11, key 12] (by simp)
  output_commitments := Std.Array.from [key 21, key 22] (by simp)

def out1 : Slice U8 := Slice.from [1#u8, 2#u8] (by scalar_tac)
def out2 : Slice U8 := Slice.from [3#u8] (by scalar_tac)

def depositAccounts : TransactAccounts where
  treeAccount := deployment.pda merkleTreeSeeds
  nullifier0 := deployment.pda (nullifier0Seeds (key 11))
  nullifier1 := deployment.pda (nullifier1Seeds (key 12))
  nullifier2 := deployment.pda (nullifier0Seeds (key 12))
  nullifier3 := deployment.pda (nullifier1Seeds (key 11))
  treeTokenAccount := deployment.pda treeTokenSeeds
  globalConfig := deployment.pda globalConfigSeeds
  recipient := key 2
  feeRecipientAccount := key 3
  signer := key 1
  systemProgram := systemProgram

def depositIx : Instruction := .transact depositAccounts depositProof ⟨200⟩ 0#u64 out1 out2

-- The toy derivation gives every account of the scenario its own address.
#guard let a := depositAccounts
  let keys := [a.treeAccount, a.nullifier0, a.nullifier1, a.nullifier2, a.nullifier3,
    a.treeTokenAccount, a.globalConfig, a.recipient, a.feeRecipientAccount, a.signer,
    a.systemProgram, deployment.programId]
  keys.dedup.length == keys.length

-- The deposit succeeds: the signer pays 200 plus the two nullifier accounts'
-- rent (9 bytes × 10 each), the pool gains 200, and the program emits one
-- `CommitmentData` per new leaf, in order: leaf 0 with the first commitment
-- and first encrypted output, leaf 1 with the second.
#guard match step deployment initialized tx depositIx with
  | .ok (s, events) =>
    (s (key 1)).lamports.val + 200 + 2 * 90 == (initialized (key 1)).lamports.val &&
    (s depositAccounts.treeTokenAccount).lamports.val ==
      (initialized depositAccounts.treeTokenAccount).lamports.val + 200 &&
    events == [⟨0#u64, key 21, [1#u8, 2#u8]⟩, ⟨1#u64, key 22, [3#u8]⟩]
  | .error _ => false

-- Replaying the same nullifiers fails: their accounts now exist.
#guard match step deployment initialized tx depositIx with
  | .ok (s, _) => isAccountsError (step deployment s tx depositIx)
  | .error _ => false

end PrivacyCash.Tests.Executable
