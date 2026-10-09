/-
The program model can be run: `step` is computable, so it can be evaluated on
concrete states, instructions and deployments. This file checks that on a
small `initialize` scenario with a toy deployment (made-up addresses and
crypto). Conformance tests against the real program (LiteSVM traces) build on
this.
-/
import PrivacyCash
open Aeneas Aeneas.Std PrivacyCash.Model

namespace PrivacyCash.Tests.Executable

/-- The address whose 32 bytes are all `b`. -/
def key (b : Nat) : Pubkey :=
  Std.Array.repeat 32#usize (U8.ofNatCore (b % 256) (by simp only [UScalarTy.numBits]; omega))

/-- A toy deployment: an address derivation that only looks at the seed
    length (enough to tell this program's PDAs apart) and crypto that is never
    exercised by `initialize` beyond `zero_bytes`. -/
def deployment : Deployment where
  programId := key 7
  createProgramAddress seeds := key (seeds.length + 100)
  canonicalBump _ := 255#u8
  crypto :=
    { hasher := { hash_pair := fun a _ => .ok a, zero_bytes := .ok (Std.Array.repeat 41#usize (key 0)) }
      sha256 := { hash := fun _ => .ok (key 0) }
      altBn128 := ⟨fun _ => none, fun _ => none, fun _ => none⟩ }
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

def isAccountsError : Except PrivacyCash.Model.Error State → Bool
  | .error .accounts => true
  | _ => false

-- `initialize` succeeds: the authority pays the three accounts' rent
-- ((4136 + 41 + 48) bytes × 10), and the program owns them.
#guard match step deployment genesis tx initIx with
  | .ok s => (s (key 1)).lamports.val == 10000000 - (4136 + 41 + 48) * 10 &&
      [merkleTreeSeeds, treeTokenSeeds, globalConfigSeeds].all fun seeds =>
        decide ((s (deployment.pda seeds)).owner = deployment.programId)
  | .error _ => false

-- A second `initialize` fails: the accounts already exist.
#guard match step deployment genesis tx initIx with
  | .ok s => isAccountsError (step deployment s tx initIx)
  | .error _ => false

-- Without the authority's signature, `initialize` fails.
#guard isAccountsError (step deployment genesis { tx with signers := [] } initIx)

end PrivacyCash.Tests.Executable
