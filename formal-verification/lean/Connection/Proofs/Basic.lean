import Connection.Mapping
open Aeneas Aeneas.Std PrivacyCash.Model

/-! # Definitions used only inside the proofs (not for review)

Helpers the connection's proofs share, kept off the review surface (`Mapping.lean`). -/

namespace Connection

/-- `withSyscallSpec C`: in a proof, sets the same three instances as the term form
    `withSyscallSpec C in t` (`Mapping.lean`). -/
macro "withSyscallSpec " C:term:max : tactic =>
  `(tactic| (letI : Spec.Groups := syscallGroups $C
             letI : Spec.Pairing := syscallPairing $C
             letI : Spec.Deployment := programDeployment $C))

/-! ## The mapping's byte readers are the code's -/

/-- The spec's big-endian reading of code bytes is the code's. -/
theorem natOfBE_toBytes (l : List U8) :
    Spec.natOfBE (toBytes l) = l.foldl (fun acc x => acc * 256 + x.val) 0 := by
  unfold Spec.natOfBE toBytes
  rw [List.foldl_map]
  congr 1; funext acc x
  show 256 * acc + x.val = acc * 256 + x.val
  ring

theorem toBytes_length (l : List U8) : (toBytes l).length = l.length := by simp [toBytes]

/-- A 32-byte array, as the spec's bytes: the spec reads the same number (`beNat`). -/
theorem natOfBE_toBytes_arr (b : Std.Array U8 32#usize) :
    Spec.natOfBE (toBytes b.val) = beNat b := natOfBE_toBytes b.val

/-- The spec's little-endian reading of code bytes is the code's (`leNatOfList`). -/
theorem natOfLE_toBytes_leNat (l : List U8) : Spec.natOfLE (toBytes l) = leNatOfList l := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [toBytes, List.map_cons, Spec.natOfLE, List.foldr_cons, leNatOfList] at ih ⊢
    rw [ih]; rfl

theorem toF_def (b : Std.Array U8 32#usize) : toF b = (beNat b : Spec.F) := by
  rw [toF, natOfBE_toBytes_arr]

theorem canonical_def (b : Std.Array U8 32#usize) : Canonical b ↔ beNat b < bn254ScalarModulus := by
  rw [Canonical, natOfBE_toBytes_arr]; rfl

theorem toPubkey_def (k : Pubkey) : toPubkey k = BitVec.ofNat 256 (leNatOfList k.val) := by
  rw [toPubkey, natOfLE_toBytes_leNat]

/-- `toSlice bs`: the spec's bytes as a code slice (empty if too long, which no real
    transaction is). -/
def toSlice (bs : Spec.Bytes) : Slice U8 :=
  let l : List U8 := bs.map (fun b => ⟨b⟩)
  if h : l.length ≤ Usize.max then Slice.from l h else Slice.from [] (by simp)


/-- `TreeShape t`: the tree fields `initialize` sets and nothing changes: height 26, 100 roots
    of history, and a root index below 100. -/
def TreeShape (t : zkcash_core.merkle_tree.MerkleTreeAccount) : Prop :=
  t.height.val = 26 ∧ t.root_history_size.val = 100 ∧ t.root_index.val < 100

/-- `nullifierAddrOf d`: `toWorld`'s nullifier account addresses, which do not depend on the
    state or the rent (`toWorld_nullifierAddr`). -/
def nullifierAddrOf (d : Deployment) (i : Fin 2) (b : Spec.Bytes) : Spec.Pubkey :=
  match toArray 32#usize b with
  | some n => toPubkey (d.nullifierAddress i n)
  | none => 0

theorem toWorld_nullifierAddr (d : Deployment) (rent : Nat → U64) (s : State) :
    (toWorld d rent s).state.nullifierAddr = nullifierAddrOf d := rfl

/-! ## Decidability (so a proof can say the code returns `decide (…)`) -/

instance (extAmt : ℤ) (f : ℕ) (pubAmt : Spec.F) :
    Decidable (Spec.pubAmtConsistent extAmt f pubAmt) := by
  unfold Spec.pubAmtConsistent; infer_instance

instance (extAmt : ℤ) (f : ℕ) : Decidable (Spec.amountsInRange extAmt f) := by
  unfold Spec.amountsInRange; infer_instance

instance (inputs : Spec.TxInputs) : Decidable (Spec.encOutsFit inputs) := by
  unfold Spec.encOutsFit; infer_instance

instance (T : Spec.Tree) (R : Spec.F) : Decidable (Spec.rootKnown T R) :=
  decidable_of_iff ((∃ i, T.history i = R) ∧ R ≠ 0) (by simp [Spec.rootKnown, Set.mem_range])

instance (T : Spec.Tree) (bs : Spec.Bytes) : Decidable (Spec.rootBytesKnown T bs) := by
  unfold Spec.rootBytesKnown; infer_instance

end Connection
