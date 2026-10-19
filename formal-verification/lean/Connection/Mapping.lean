import PrivacyCash
import Spec.privacy_cash_spec
open Aeneas Aeneas.Std PrivacyCash.Model

/-! # Mapping: code-model values to spec values

REVIEW SURFACE. The connection theorem (`Connection/Transact.lean`) says: when the code
model accepts a `transact`, the spec's `transact` holds between the mapped worlds. Its
meaning depends on these definitions, so each is short and should be checked by reading.

A mapping that throws information away could make the theorem easier to prove but weaker.
Every map below is injective on the values that matter, except where its comment says
otherwise (field elements are read mod p; nullifier accounts are left out of the balances).
-/

namespace Connection

/-! ## Values -/

/-- A 32-byte public input or hash, as a field element: read big-endian, reduced mod p.
    (The verifier reads public inputs big-endian, and rejects values `≥ p`.) -/
def toF (b : Std.Array U8 32#usize) : LeanSpec.F := (beNat b : LeanSpec.F)

/-- Bytes whose big-endian value is below the field modulus, so `toF` loses nothing. -/
def Canonical (b : Std.Array U8 32#usize) : Prop := beNat b < bn254ScalarModulus

/-- Bytes, as the spec's bytes. -/
def toBytes (l : List U8) : LeanSpec.Bytes := l.map (·.bv)

/-- The spec's bytes as a code byte slice (empty if too long for a slice, which no real
    transaction is). Used to say which bytes the code hashes. -/
def toSlice (bs : LeanSpec.Bytes) : Slice U8 :=
  let l : List U8 := bs.map (fun b => ⟨b⟩)
  if h : l.length ≤ Usize.max then Slice.from l h else Slice.from [] (by simp)

/-- A Solana address, as the spec's `Pubkey`: read little-endian, so that the spec's
    serialization `PubkeyToBytes` gives back the address's own 32 bytes. -/
def toPubkey (k : Pubkey) : LeanSpec.Pubkey := BitVec.ofNat 256 (leNatOfList k.val)

/-- The inverse of `toPubkey`. -/
def fromPubkey (x : LeanSpec.Pubkey) : Pubkey :=
  Std.Array.from (leBytes32 x.toNat) (by simp [leBytes32])

/-! ## The program's accounts -/

/-- The SOL tree, the pool and the config live at their canonical addresses. -/
def treeAddr (d : Deployment) : Pubkey := d.pda merkleTreeSeeds
def poolAddr (d : Deployment) : Pubkey := d.pda treeTokenSeeds
def configAddr (d : Deployment) : Pubkey := d.pda globalConfigSeeds

/-- The tree stored at `k` (all zeros if there is none; `WellFormed` rules that out). -/
def treeAt (s : State) (k : Pubkey) : zkcash_core.merkle_tree.MerkleTreeAccount :=
  match (s k).data with
  | .treeAccount t => t
  | _ => zeroTree

/-- The config stored at `k` (all zeros if there is none). -/
def configAt (s : State) (k : Pubkey) : zkcash_core.admin.GlobalConfig :=
  match (s k).data with
  | .globalConfig c => c
  | _ => ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩

/-- The tree account fields `initialize` sets and no instruction changes: height 26, a
    history of 100 roots, and a current root index inside it. -/
def TreeShape (t : zkcash_core.merkle_tree.MerkleTreeAccount) : Prop :=
  t.height.val = 26 ∧ t.root_history_size.val = 100 ∧ t.root_index.val < 100

/-- The tree account, field by field. `rootIndex` is reduced mod 100; `WellFormed` says it
    is already below 100. -/
def toTree (t : zkcash_core.merkle_tree.MerkleTreeAccount) : LeanSpec.Tree where
  nextIndex := t.next_index.val
  subtrees i := toF (t.subtrees.val[i.val]!)
  root := toF t.root
  history i := toF (t.root_history.val[i.val]!)
  rootIndex := ⟨t.root_index.val % 100, Nat.mod_lt _ (by decide)⟩

/-- The config, field by field. The deposit limit lives on the tree account in the code. -/
def toConfig (c : zkcash_core.admin.GlobalConfig)
    (t : zkcash_core.merkle_tree.MerkleTreeAccount) : LeanSpec.config where
  authority := toPubkey c.authority
  depositFeeRate := c.deposit_fee_rate.val
  withdrawalFeeRate := c.withdrawal_fee_rate.val
  feeMarginError := c.fee_error_margin.val
  maxDepositLimit := t.max_deposit_amount.val

/-! ## Worlds -/

/-- The balance the spec sees for account `k`: its lamports, except that nullifier accounts
    count as 0. MAPPING DECISION: the spec's balances are those of public accounts, and the
    signer's nullifier rent leaves them (spec G4a: "no SOL is created or lost, except the
    nullifier rent"). On-chain that rent goes to the two new nullifier accounts. -/
def publicBalance (s : State) (k : Pubkey) : ℕ :=
  match (s k).data with
  | .nullifier _ => 0
  | _ => (s k).lamports.val

/-- The spec world a chain state stands for.
    * `rent`: Solana's rent-exempt minimum for an account of a given size. The spec fixes the
      two amounts it uses; `Assumed.rentFixed` says each transaction sees this `rent`.
    * `spent`: the spent nullifiers, tracked alongside the chain. On-chain a nullifier is
      spent when its nullifier account exists; `WellFormed.spentRecorded` links the two. -/
def toWorld (d : Deployment) (rent : Nat → U64) (spent : Finset LeanSpec.F) (s : State) :
    LeanSpec.World where
  state :=
    { tree := toTree (treeAt s (treeAddr d))
      nullifiers := spent
      pool := toPubkey (poolAddr d)
      config := toConfig (configAt s (configAddr d)) (treeAt s (treeAddr d)) }
  balances x := publicBalance s (fromPubkey x)
  rentExemptMin := (rent treeTokenAccountSpace).val
  nullifierRent := (rent nullifierAccountSpace).val

/-! ## Transactions -/

variable [LeanSpec.Groups]

/-- The spec inputs of a `transact` instruction. `π` is the proof as spec group elements;
    until the verifier bridge is built it is a free parameter, tied to `proof` only by the
    connection theorem's `hProofValid`. -/
def toInputs (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (extAmount : I64)
    (fee : U64) (out1 out2 : Slice U8) (π : LeanSpec.Groth16.Proof) : LeanSpec.TxInputs where
  R := toF proof.root
  pubAmt := toF proof.public_amount
  extDataHash := toF proof.ext_data_hash
  k0 := toF proof.input_nullifiers.val[0]!
  k1 := toF proof.input_nullifiers.val[1]!
  outC0 := toF proof.output_commitments.val[0]!
  outC1 := toF proof.output_commitments.val[1]!
  extAmt := extAmount.val
  f := fee.val
  s := toPubkey a.signer
  A := toPubkey a.recipient
  t := toPubkey a.feeRecipientAccount
  encOut0 := toBytes out1.val
  encOut1 := toBytes out2.val
  π := π
  mintAddr := toPubkey zkcash_core.transact.SOL_ADDRESS

/-! ## The verifier: the spec instantiated by the syscalls and the program's key

The spec's groups, pairing, deployed key and proof points, for the verifier bridge. The
groups `G1 G2 GT`, the point decoding come from the syscall contracts
`C` (core-model's `AltBn128Contracts`); the key is the program's extracted `VERIFYING_KEY`. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] {s : AltBn128}
open PrivacyCash.Proofs.Groth16 (ic)

/-- The spec's groups: the syscalls'. -/
@[reducible] def syscallGroups (G1 G2 GT : Type) : LeanSpec.Groups := ⟨G1, G2, GT⟩

/-- The spec's deployed key: the program's key, as the syscalls decode it. -/
@[reducible] def programKey (C : AltBn128Contracts s G1 G2 GT) :
    @LeanSpec.Groth16.VerificationKey (syscallGroups G1 G2 GT) :=
  letI : LeanSpec.Groups := syscallGroups G1 G2 GT
  let vk := zkcash_core.verifying_key.VERIFYING_KEY
  { α := (C.decodeG1 vk.vk_alpha_g1).getD 0, β := (C.decodeG2 vk.vk_beta_g2).getD 0,
    γ := (C.decodeG2 vk.vk_gamme_g2).getD 0, δ := (C.decodeG2 vk.vk_delta_g2).getD 0,
    IC := fun i => ic C vk i.val }

/-- The spec's proof: the proof's points, as the syscalls decode them. -/
@[reducible] def proofPoints (C : AltBn128Contracts s G1 G2 GT) (proof : zkcash_core.transact.Proof) :
    @LeanSpec.Groth16.Proof (syscallGroups G1 G2 GT) :=
  letI : LeanSpec.Groups := syscallGroups G1 G2 GT
  { A := (C.decodeG1 proof.proof_a).getD 0, B := (C.decodeG2 proof.proof_b).getD 0,
    C := (C.decodeG1 proof.proof_c).getD 0 }

end

/-! ## Decidability (so a statement can say the code returns `decide (spec predicate)`) -/

/-- The spec's field and the code's field are the same, `ZMod p` with the same `p`. -/
theorem p_eq : LeanSpec.p = bn254ScalarModulus := rfl

instance (extAmt : ℤ) (f : ℕ) (pubAmt : LeanSpec.F) :
    Decidable (LeanSpec.pubAmtConsistent extAmt f pubAmt) := by
  unfold LeanSpec.pubAmtConsistent; infer_instance

instance (inputs : LeanSpec.TxInputs) : Decidable (LeanSpec.encOutsFit inputs) := by
  unfold LeanSpec.encOutsFit; infer_instance

instance (T : LeanSpec.Tree) (R : LeanSpec.F) : Decidable (LeanSpec.rootKnown T R) :=
  decidable_of_iff ((∃ i, T.history i = R) ∧ R ≠ 0) (by simp [LeanSpec.rootKnown, Set.mem_range])

end Connection
