import PrivacyCash
import Spec.Statements
open Aeneas Aeneas.Std PrivacyCash.Model

/-! # Mapping: code-model values to spec values

REVIEW SURFACE. The connection theorems (`Connection/Statements.lean`) say: when the code
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
      two amounts it uses; `OutsideSpecDetail.rentFixed` says each transaction sees this `rent`.
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

/-- The spec inputs of a `transact` instruction. The seven public inputs are given twice, as
    the spec's field elements (`toF`) and as the sender's 32 bytes (`pubInputBytes`, in
    circuit order, `publicInputs`); the proof is the sender's bytes of its three points. -/
def toInputs (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (extAmount : I64)
    (fee : U64) (out1 out2 : Slice U8) : LeanSpec.TxInputs where
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
  π := ⟨toBytes proof.proof_a.val, toBytes proof.proof_b.val, toBytes proof.proof_c.val⟩
  mintAddr := toPubkey zkcash_core.transact.SOL_ADDRESS
  pubInputBytes i := toBytes ((publicInputs proof)[i.val]!).val

/-! ## The handler's view (for handler completeness)

The extracted `transact` handler runs after Anchor's account checks and `init`s, on the
runtime environment `execTransact` builds. Handler completeness compares it with the spec
`transact` from the world the handler sees. -/

/-- The runtime environment the handler runs in, exactly as `execTransact` builds it: the state
    `s₁` after Anchor's two `init`s, the instruction's accounts, the rent-exempt minimum `v`. -/
def handlerEnv (a : TransactAccounts) (s₁ : State) (v : U64) : SolEnv :=
  { accounts := s₁, balances := s₁.balances, signer := a.signer,
    treeToken := a.treeTokenAccount, recipient := a.recipient,
    feeRecipient := a.feeRecipientAccount, rentExemptMinimum := some v }

/-- The spec world the handler sees: every account's lamports in `s₁`, the tree and config it
    is given, the pool's address, the rent-exempt minimum `v`, the nullifiers `spent` (the
    handler does not read them). MAPPING DECISION: `nullifierRent := 0`, because Anchor has
    already paid the two nullifier accounts' rent before the handler runs; the handler's
    effects are the spec's transfer and fee effects.
    How it differs from `toWorld` (the main theorem's world): it is taken after Anchor's two
    `init`s, not before; it reads every account's raw lamports, nullifier accounts included
    (`toWorld` counts those as 0, `publicBalance`), since the handler never pays them in the
    cases it covers; and its rent is the handler's own `v`. Used only by handler
    completeness. -/
def handlerWorld (a : TransactAccounts) (s₁ : State) (v : U64)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (config : zkcash_core.admin.GlobalConfig)
    (spent : Finset LeanSpec.F) : LeanSpec.World where
  state :=
    { tree := toTree tree
      nullifiers := spent
      pool := toPubkey a.treeTokenAccount
      config := toConfig config tree }
  balances x := (s₁ (fromPubkey x)).lamports.val
  rentExemptMin := v.val
  nullifierRent := 0

/-! ## The verifier: the spec instantiated by the syscalls and the program's key

The spec's groups, point decoding, pairing and deployed key, for the verifier bridge. The
groups `G1 G2 GT` and the point decoding come from the syscall contracts `C` (core-model's
`AltBn128Contracts`); the key is the program's extracted `VERIFYING_KEY`. -/

/-- The spec's bytes as an `n`-byte code array, if there are exactly `n` of them. -/
def toArray (n : Usize) (bs : LeanSpec.Bytes) : Option (Std.Array U8 n) :=
  if h : bs.length = n.val then
    some (Std.Array.from (bs.map (fun b => (⟨b⟩ : U8))) (by simp [h]))
  else none

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] {s : AltBn128}
open PrivacyCash.Proofs.Groth16 (ic)

/-- The spec's groups and point decoding: the syscalls'. A G1 point is 64 bytes and a G2 point
    128 bytes, decoded as the syscalls decode them (`C.decodeG1`, `C.decodeG2`); bytes of any
    other length are not a point. -/
@[reducible] def syscallGroups (C : AltBn128Contracts s G1 G2 GT) : LeanSpec.Groups :=
  ⟨G1, G2, GT, fun bs => (toArray 64#usize bs).bind C.decodeG1,
    fun bs => (toArray 128#usize bs).bind C.decodeG2⟩

/-- The spec's deployed key: the program's key, as the syscalls decode it. The key is the
    program's own constant, not sender data; whenever the verifier accepts a proof, every one
    of its points decodes (`programVerifier_groth16`), so the default `0` is never used. -/
@[reducible] def programKey (C : AltBn128Contracts s G1 G2 GT) :
    @LeanSpec.Groth16.VerificationKey (syscallGroups C) :=
  letI : LeanSpec.Groups := syscallGroups C
  let vk := zkcash_core.verifying_key.VERIFYING_KEY
  { α := (C.decodeG1 vk.vk_alpha_g1).getD 0, β := (C.decodeG2 vk.vk_beta_g2).getD 0,
    γ := (C.decodeG2 vk.vk_gamme_g2).getD 0, δ := (C.decodeG2 vk.vk_delta_g2).getD 0,
    IC := fun i => ic C vk i.val }

end

/-! ## Decidability (so a statement can say the code returns `decide (spec predicate)`) -/

/-- The spec's field and the code's field are the same, `ZMod p` with the same `p`. -/
theorem p_eq : LeanSpec.p = bn254ScalarModulus := rfl

instance (extAmt : ℤ) (f : ℕ) (pubAmt : LeanSpec.F) :
    Decidable (LeanSpec.pubAmtConsistent extAmt f pubAmt) := by
  unfold LeanSpec.pubAmtConsistent; infer_instance

instance (extAmt : ℤ) (f : ℕ) : Decidable (LeanSpec.amountsInRange extAmt f) := by
  unfold LeanSpec.amountsInRange; infer_instance

instance (inputs : LeanSpec.TxInputs) : Decidable (LeanSpec.encOutsFit inputs) := by
  unfold LeanSpec.encOutsFit; infer_instance

instance (T : LeanSpec.Tree) (R : LeanSpec.F) : Decidable (LeanSpec.rootKnown T R) :=
  decidable_of_iff ((∃ i, T.history i = R) ∧ R ≠ 0) (by simp [LeanSpec.rootKnown, Set.mem_range])

instance (T : LeanSpec.Tree) (bs : LeanSpec.Bytes) : Decidable (LeanSpec.rootBytesKnown T bs) := by
  unfold LeanSpec.rootBytesKnown; infer_instance

end Connection
