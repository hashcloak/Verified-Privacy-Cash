import Connection.Proofs.Checks
import Connection.Hypotheses
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: the Merkle tree append

NOT FOR REVIEW: the statements are restated in `Connection/ConnectionTheorems.lean`. Ported from the
connection to the earlier `fv_*` model (commit e862db8, `Connection/TransactSafety.lean`). -/

namespace Connection
open zkcash_core

theorem bindOk {α β : Type} {m : Result α} {f : α → Result β} {v : β}
    (h : (do let x ← m; f x) = ok v) : ∃ x, m = ok x ∧ f x = ok v :=
  PrivacyCash.Proofs.G1.bind_eq_ok' h

/-- **Partial correctness of a loop**: if the loop returned `y`, and every step that returns
    keeps `inv` and decreases `measure` (or finishes with `post`), then `post y`. Unlike
    Aeneas's `loop.spec`, this needs nothing about steps that fail, which is what safety
    statements need (a hash that might fail on some inputs). -/
theorem loop_ok_induction {α β : Type} (body : α → Result (ControlFlow α β)) (measure : α → ℕ)
    (inv : α → Prop) (post : β → Prop)
    (hstep : ∀ x r, inv x → body x = ok r →
      match r with
      | .done y => post y
      | .cont x' => inv x' ∧ measure x' < measure x) :
    ∀ x y, inv x → loop body x = ok y → post y := by
  intro x
  induction hm : measure x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    intro y hinv h
    rw [loop] at h
    obtain ⟨r, hr, hk⟩ := bindOk h
    have hs := hstep x r hinv hr
    cases r with
    | cont x' =>
      exact ih (measure x') (hm ▸ hs.2) x' rfl y hs.1 hk
    | done y' =>
      have : y' = y := Result.ok_injective hk
      subst this; exact hs

private theorem cloneUsize : ∀ x : Usize, core.clone.CloneUsize.clone x = ok x := by
  intro x; simp

private theorem ltUsize : ∀ a b : Usize, core.cmp.PartialOrdUsize.lt a b = ok (decide (a.val < b.val)) := by
  intro a b; simp [core.cmp.impls.PartialOrdUsize.lt]; try rfl

/-! ## The spec's append, as a fold over `ℕ` -/

def natFold {α : Type} (g : α → ℕ → α) (x : α) : ℕ → α
  | 0 => x
  | k + 1 => g (natFold g x k) k

theorem finFoldlNat {α : Type} (g : α → ℕ → α) :
    ∀ (n : ℕ) (x : α), Fin.foldl n (fun a (j : Fin n) => g a j.val) x = natFold g x n
  | 0, x => by simp [natFold]
  | n + 1, x => by
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [finFoldlNat g n x]; rfl

private theorem okOf {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : ∃ x, m = ok x ∧ P x :=
  (WP.spec_equiv_exists _ _).mp h

variable [Spec.PoseidonHashes]

/-- One level of `appendEffects`'s fold (levels `≥ 26` are no-ops). -/
def appendLevel (index : ℕ) (acc : Spec.F × (Fin 26 → Spec.F)) (j : ℕ) :
    Spec.F × (Fin 26 → Spec.F) :=
  if hj : j < 26 then
    if Nat.testBit index j then (Spec.PoseidonHashes.H2 (acc.2 ⟨j, hj⟩) acc.1, acc.2)
    else (Spec.PoseidonHashes.H2 acc.1 (Spec.Z j), Function.update acc.2 ⟨j, hj⟩ acc.1)
  else acc

theorem appendEffectsFold (c : Spec.F) (t : Spec.Tree) :
    Spec.appendEffects c t =
      let r := natFold (appendLevel t.nextIndex) (c, t.subtrees) 26
      { nextIndex := t.nextIndex + 1, subtrees := r.2, root := r.1,
        history := Function.update t.history (t.rootIndex + 1) r.1,
        rootIndex := t.rootIndex + 1 } := by
  have hf : ∀ x, Fin.foldl 26 (fun (p : Spec.F × (Fin 26 → Spec.F)) (height : Fin 26) =>
      match p with
      | (current, subtrees) =>
        if Nat.testBit t.nextIndex height.val then
          (Spec.PoseidonHashes.H2 (subtrees height) current, subtrees)
        else (Spec.PoseidonHashes.H2 current (Spec.Z height.val),
          Function.update subtrees height current)) x
      = natFold (appendLevel t.nextIndex) x 26 := by
    intro x
    rw [← finFoldlNat]
    congr 1; funext acc j; obtain ⟨cur, sub⟩ := acc
    simp [appendLevel, j.isLt]
  simp only [Spec.appendEffects, hf]

/-- The 26 stored subtrees, as field elements. -/
def subtreesF (a : Std.Array (Std.Array U8 32#usize) 26#usize) : Fin 26 → Spec.F :=
  fun j => toF a.val[j.val]!

omit [Spec.PoseidonHashes] in
theorem subtreesF_set (a : Std.Array (Std.Array U8 32#usize) 26#usize) (i : Usize)
    (v : Std.Array U8 32#usize) (hi : i.val < 26) :
    subtreesF (a.set i v) = Function.update (subtreesF a) ⟨i.val, hi⟩ (toF v) := by
  funext j
  have hlen : a.val.length = 26 := by simp
  by_cases hj : j = ⟨i.val, hi⟩
  · subst hj
    simp only [subtreesF, Function.update_self, Std.Array.set_val_eq]
    rw [getElem!_pos _ _ (by simpa [hlen] using hi)]
    simp
  · have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp only [subtreesF, Function.update_of_ne hj, Std.Array.set_val_eq]
    rw [getElem!_pos _ _ (by simp [hlen]), getElem!_pos _ _ (by simp [hlen])]
    simp [Ne.symm hj']


omit [Spec.PoseidonHashes] in
/-- Setting a canonical value in an array of canonical values keeps them canonical. -/
theorem set_canonical (a : Std.Array (Std.Array U8 32#usize) 26#usize) (i : Usize)
    (v : Std.Array U8 32#usize) (_hi : i.val < 26)
    (ha : ∀ j, j < 26 → Canonical (a.val[j]!)) (hv : Canonical v) :
    ∀ j, j < 26 → Canonical ((a.set i v).val[j]!) := by
  intro j hj
  simp only [Std.Array.set_val_eq]
  by_cases hji : j = i.val
  · rw [getElem!_pos _ _ (by simp; omega)]; simp [hji]; exact hv
  · rw [getElem!_pos _ _ (by simp; omega)]
    have := ha j hj
    rw [getElem!_pos _ _ (by simp; omega)] at this
    have hne : i.val ≠ j := Ne.symm hji
    simpa [hne] using this

/-- **The append loop computes the spec's fold**, if it returns. It hashes only canonical
    values: the current hash, the subtrees and the zero hashes stay canonical. -/
theorem appendLoop_ok (H : merkle_tree.Hasher Unit)
    (hp : ∀ a b h, Canonical a → Canonical b → H.hash_pair a b = ok h →
      Canonical h ∧ toF h = Spec.PoseidonHashes.H2 (toF a) (toF b))
    (z : _) (hzb : H.zero_bytes = ok z)
    (hZ : ∀ i, i ≤ 26 → Canonical (z.val[i]!) ∧ toF (z.val[i]!) = Spec.Z i)
    (index : ℕ) (init : Spec.F × (Fin 26 → Spec.F))
    (iter : core.ops.range.Range Usize) (a : Std.Array (Std.Array U8 32#usize) 26#usize)
    (ci : Usize) (cur : Std.Array U8 32#usize) (proof : alloc.vec.Vec (Std.Array U8 32#usize))
    (r : (Std.Array (Std.Array U8 32#usize) 26#usize) × (Std.Array U8 32#usize) ×
      (alloc.vec.Vec (Std.Array U8 32#usize)))
    (hk : iter.start.val ≤ 26) (hend : iter.end.val = 26)
    (hci : ci.val = index / 2 ^ iter.start.val) (hplen : proof.length = 26)
    (ha : ∀ i, i < 26 → Canonical (a.val[i]!)) (hcur : Canonical cur)
    (hst : (toF cur, subtreesF a) = natFold (appendLevel index) init iter.start.val)
    (h : merkle_tree.append_loop H iter a ci cur proof = ok r) :
    (toF r.2.1, subtreesF r.1) = natFold (appendLevel index) init 26 := by
  unfold merkle_tree.append_loop at h
  refine loop_ok_induction _
    (fun x : (core.ops.range.Range Usize) × (Std.Array (Std.Array U8 32#usize) 26#usize)
        × Usize × (Std.Array U8 32#usize) × (alloc.vec.Vec (Std.Array U8 32#usize)) =>
      26 - x.1.start.val)
    (fun x => x.1.start.val ≤ 26 ∧ x.1.end.val = 26 ∧
      x.2.2.1.val = index / 2 ^ x.1.start.val ∧ x.2.2.2.2.length = 26 ∧
      ((∀ i, i < 26 → Canonical (x.2.1.val[i]!)) ∧ Canonical x.2.2.2.1) ∧
      (toF x.2.2.2.1, subtreesF x.2.1) = natFold (appendLevel index) init x.1.start.val)
    (fun r => (toF r.2.1, subtreesF r.1) = natFold (appendLevel index) init 26)
    ?_ _ r ⟨hk, hend, hci, hplen, ⟨ha, hcur⟩, hst⟩ h
  rintro ⟨it, a, ci, cur, proof⟩ rr ⟨hk, hend, hci, hplen, ⟨ha, hcur⟩, hst⟩ hr
  simp only at hk hend hci hplen ha hcur hst
  unfold merkle_tree.append_loop.body at hr
  simp only [core.iter.range.StepUsize] at hr
  by_cases hlt : it.start.val < 26
  · obtain ⟨⟨o, it1⟩, hn, ho, hs1, he1⟩ := okOf
      (core.iter.range.IteratorRange.next_UScalar_some_spec cloneUsize ltUsize it (by omega))
    rw [hn, bind_tc_ok] at hr
    subst ho
    -- peel the steps one by one (unification sees through the `let`-matches)
    obtain ⟨⟨sub, back⟩, hix, hr⟩ := bindOk hr
    obtain ⟨⟨sub', back'⟩, hix', hsub, hback⟩ := okOf (Std.Array.index_mut_usize_spec a it.start (by simp; omega))
    rw [hix'] at hix
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hix)
    obtain ⟨z', hz', hr⟩ := bindOk hr
    rw [hzb] at hz'; obtain rfl := Result.ok_injective hz'
    obtain ⟨zb, hzi, hr⟩ := bindOk hr
    obtain ⟨zb', hzi', hzbv⟩ := okOf (Std.Array.index_usize_spec z it.start (by simp; omega))
    rw [hzi'] at hzi; obtain rfl := Result.ok_injective hzi
    obtain ⟨c2, hc2, hr⟩ := bindOk hr
    obtain ⟨c2', hc2', hc2v⟩ := okOf (UScalar.rem_spec ci (y := 2#usize) (by simp))
    rw [hc2'] at hc2; obtain rfl := Result.ok_injective hc2
    obtain ⟨⟨left, right, proof1⟩, hlr, hr⟩ := bindOk hr
    obtain ⟨hv, hhash, hr⟩ := bindOk hr
    obtain ⟨ci', hci', hr⟩ := bindOk hr
    obtain ⟨ci'', hci'', hci'v⟩ := UScalar.div_spec ci (y := 2#usize) (by simp)
    rw [hci''] at hci'; obtain rfl := Result.ok_injective hci'
    have hrr := (Result.ok_injective hr).symm
    subst hrr
    have hs26 : it.start.val < 26 := hlt
    have hzval : Canonical zb' ∧ toF zb' = Spec.Z it.start.val := by
      have := hZ it.start.val (by omega)
      rw [getElem!_pos _ _ (by simp; omega)] at this
      rw [hzbv]; exact this
    have hsubc : Canonical sub' := by
      have := ha it.start.val hs26
      rw [getElem!_pos _ _ (by simp; omega)] at this
      rw [hsub]; exact this
    have hnext : ci''.val = index / 2 ^ it1.start.val := by
      rw [hci'v, hs1, hci, Nat.div_div_eq_div_mul, pow_succ]; rfl
    have h2v : ((2#usize : Usize).val) = 2 := by simp
    rw [h2v] at hc2v
    have hb26 : it1.start.val ≤ 26 := by omega
    have hmeas : 26 - it1.start.val < 26 - it.start.val := by omega
    by_cases hev : c2' = 0#usize
    · rw [if_pos hev] at hlr
      obtain ⟨⟨x, back1⟩, hvm, hlr⟩ := bindOk hlr
      obtain ⟨⟨x', back1'⟩, hvm', -, hb1⟩ := okOf (alloc.vec.Vec.index_mut_usize_spec proof it.start
        (by simp [hplen]; omega))
      rw [alloc.vec.Vec.index_mut_slice_index, hvm'] at hvm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hvm)
      obtain ⟨rfl, rfl, rfl⟩ : cur = left ∧ zb' = right ∧ back1' zb' = proof1 := by
        have := Result.ok_injective hlr; simp only [Prod.mk.injEq] at this; exact this
      have hbit : Nat.testBit index it.start.val = false := by
        rw [Nat.testBit_eq_decide_div_mod_eq, ← hci]
        have : c2'.val = 0 := by rw [hev]; rfl
        rw [hc2v] at this; simp [this]
      obtain ⟨hvc, hveq⟩ := hp _ _ _ hcur hzval.1 hhash
      refine ⟨⟨hb26, by rw [he1]; exact hend, hnext, by rw [hb1]; simpa using hplen,
        ⟨by rw [hback]; exact set_canonical _ _ _ hs26 ha hcur, hvc⟩, ?_⟩, hmeas⟩
      show (toF hv, subtreesF (back' cur)) = natFold (appendLevel index) init it1.start.val
      rw [hs1, natFold, ← hst, hback, subtreesF_set _ _ _ hs26, hveq, hzval.2]
      simp only [appendLevel, dif_pos hs26, hbit, Bool.false_eq_true, ↓reduceIte]
    · rw [if_neg hev] at hlr
      obtain ⟨⟨x, back1⟩, hvm, hlr⟩ := bindOk hlr
      obtain ⟨⟨x', back1'⟩, hvm', -, hb1⟩ := okOf (alloc.vec.Vec.index_mut_usize_spec proof it.start
        (by simp [hplen]; omega))
      rw [alloc.vec.Vec.index_mut_slice_index, hvm'] at hvm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hvm)
      obtain ⟨rfl, rfl, rfl⟩ : sub' = left ∧ cur = right ∧ back1' sub' = proof1 := by
        have := Result.ok_injective hlr; simp only [Prod.mk.injEq] at this; exact this
      have hbit : Nat.testBit index it.start.val = true := by
        rw [Nat.testBit_eq_decide_div_mod_eq, ← hci]
        have h1 : c2'.val ≠ 0 := fun h0 => hev (by scalar_tac)
        rw [hc2v] at h1
        simp; omega
      have hsubF : toF sub' = subtreesF a ⟨it.start.val, hs26⟩ := by
        simp only [subtreesF, hsub]
        rw [getElem!_pos _ _ (by simp; omega)]
      obtain ⟨hvc, hveq⟩ := hp _ _ _ hsubc hcur hhash
      refine ⟨⟨hb26, by rw [he1]; exact hend, hnext, by rw [hb1]; simpa using hplen,
        ⟨by rw [hback]; exact set_canonical _ _ _ hs26 ha hsubc, hvc⟩, ?_⟩, hmeas⟩
      show (toF hv, subtreesF (back' sub')) = natFold (appendLevel index) init it1.start.val
      rw [hs1, natFold, ← hst, hback, subtreesF_set _ _ _ hs26, hveq, hsubF,
        Function.update_eq_self]
      simp only [appendLevel, dif_pos hs26, hbit, ↓reduceIte]
  · obtain ⟨⟨o, it1⟩, hn, ho, hit⟩ := okOf
      (core.iter.range.IteratorRange.next_UScalar_none_spec ltUsize it (by omega))
    rw [hn, bind_tc_ok] at hr
    subst ho
    have hrr := (Result.ok_injective hr).symm
    subst hrr
    show (toF cur, subtreesF a) = natFold (appendLevel index) init 26
    have h26 : it.start.val = 26 := by omega
    rw [h26] at hst; exact hst


omit [Spec.PoseidonHashes] in
theorem histF_set (a : Std.Array (Std.Array U8 32#usize) 100#usize) (i : Usize)
    (v : Std.Array U8 32#usize) (hi : i.val < 100) :
    (fun j : Fin 100 => toF (a.set i v).val[j.val]!)
      = Function.update (fun j : Fin 100 => toF a.val[j.val]!) ⟨i.val, hi⟩ (toF v) := by
  funext j
  have hlen : a.val.length = 100 := by simp
  by_cases hj : j = ⟨i.val, hi⟩
  · subst hj
    simp only [Function.update_self, Std.Array.set_val_eq]
    rw [getElem!_pos _ _ (by simpa [hlen] using hi)]
    simp
  · have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp only [Function.update_of_ne hj, Std.Array.set_val_eq]
    rw [getElem!_pos _ _ (by simp [hlen]), getElem!_pos _ _ (by simp [hlen])]
    simp [Ne.symm hj']

omit [Spec.PoseidonHashes] in
private theorem usize_big : 2 ^ 26 ≤ 2 ^ UScalarTy.Usize.numBits :=
  Nat.pow_le_pow_right (by norm_num)
    (by cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits])

omit [Spec.PoseidonHashes] in
/-- `x.ok_or e` followed by `?`, on a `some`: continues with the value. -/
private theorem okOr_some {T β : Type} (v : T) (e : error.ErrorCode)
    (k : core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible error.ErrorCode) T → Result β)
    {w : β}
    (h : (do let r ← core.option.Option.ok_or (some v) e
             let cf ← core.result.Result.Insts.CoreOpsTry.branch r
             k cf) = ok w) :
    k (.Continue v) = ok w := by
  obtain ⟨r, hr, h⟩ := bindOk h
  obtain rfl : core.result.Result.Ok v = r := by
    simpa [core.option.Option.ok_or] using hr
  obtain ⟨cf, hcf, h⟩ := bindOk h
  obtain rfl : core.ops.control_flow.ControlFlow.Continue v = cf := by
    simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf
  exact h

omit [Spec.PoseidonHashes] in
/-- `x.ok_or e` followed by `?`, on a `none`: continues with the error. -/
private theorem okOr_none {T β : Type} (e : error.ErrorCode)
    (k : core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible error.ErrorCode) T → Result β)
    {w : β}
    (h : (do let r ← core.option.Option.ok_or (none : Option T) e
             let cf ← core.result.Result.Insts.CoreOpsTry.branch r
             k cf) = ok w) :
    k (.Break (.Err e)) = ok w := by
  obtain ⟨r, hr, h⟩ := bindOk h
  obtain rfl : core.result.Result.Err e = r := by
    simpa [core.option.Option.ok_or] using hr
  obtain ⟨cf, hcf, h⟩ := bindOk h
  obtain rfl : core.ops.control_flow.ControlFlow.Break (core.result.Result.Err e) = cf := by
    simpa [core.result.Result.Insts.CoreOpsTry.branch] using hcf
  exact h

/-- **If `append` returns `Ok`, the new tree is the spec's `appendEffects`**, there was room
    (`next_index < 2^26`), the tree keeps its shape, and the other fields are unchanged. -/
theorem append_ok (H : merkle_tree.Hasher Unit)
    (hp : ∀ a b h, Canonical a → Canonical b → H.hash_pair a b = ok h →
      Canonical h ∧ toF h = Spec.PoseidonHashes.H2 (toF a) (toF b))
    (z : _) (hzb : H.zero_bytes = ok z)
    (hZ : ∀ i, i ≤ 26 → Canonical (z.val[i]!) ∧ toF (z.val[i]!) = Spec.Z i)
    (leaf : Std.Array U8 32#usize) (t t' : merkle_tree.MerkleTreeAccount)
    (p : alloc.vec.Vec (Std.Array U8 32#usize)) (hshape : TreeShape t)
    (hsub : ∀ i, i < 26 → Canonical (t.subtrees.val[i]!)) (hleaf : Canonical leaf)
    (h : merkle_tree.append H leaf t = ok (.Ok p, t')) :
    toTree t' = Spec.appendEffects (toF leaf) (toTree t) ∧ TreeShape t' ∧
      t.next_index.val < 2 ^ 26 ∧ t'.next_index.val = t.next_index.val + 1 ∧
      t'.authority = t.authority ∧ t'.max_deposit_amount = t.max_deposit_amount ∧
      t'.bump = t.bump := by
  obtain ⟨hheight, hsize, hidx⟩ := hshape
  unfold merkle_tree.append at h
  have hhu : (UScalar.cast .Usize t.height).val = 26 := by simp [hheight]
  have hsu : (UScalar.cast .Usize t.root_history_size).val = 100 := by simp [hsize]
  obtain ⟨hu, hhu', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.height = hu := Result.ok_injective hhu'
  obtain ⟨rs, hrs', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.root_history_size = rs := Result.ok_injective hrs'
  obtain ⟨mc, hmc, h⟩ := bindOk h
  obtain ⟨mc', hmc', hmcv, -⟩ := okOf (UScalar.ShiftLeft_spec 1#u64 (UScalar.cast .Usize t.height)
    (2 ^ 64) (by rw [hhu]; decide) (by simp [U64.size, U64.numBits]))
  rw [hmc'] at hmc; obtain rfl := Result.ok_injective hmc
  have hmcV : mc'.val = 2 ^ 26 := by rw [hmcv, hhu]; decide
  by_cases hroom : t.next_index < mc'
  swap
  · rw [if_neg hroom] at h
    have := Result.ok_injective h; simp at this
  rw [if_pos hroom] at h
  have hroomV : t.next_index.val < 2 ^ 26 := by rw [← hmcV]; exact hroom
  have hciv : (UScalar.cast .Usize t.next_index).val = t.next_index.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := usize_big; omega)
  obtain ⟨ci, hci', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.next_index = ci := Result.ok_injective hci'
  obtain ⟨pr, hpr, h⟩ := bindOk h
  have hclone : (core.clone.CloneArray 32#usize core.clone.CloneU8).clone (Std.Array.repeat 32#usize 0#u8)
      = ok (Std.Array.repeat 32#usize 0#u8) := by
    obtain ⟨a', ha', heq⟩ := okOf (core.array.CloneArray.clone_spec core.clone.CloneU8
      (Std.Array.repeat 32#usize 0#u8) (by intro x _; rfl))
    show core.array.CloneArray.clone core.clone.CloneU8 _ = _
    rw [ha', ← heq]
  obtain ⟨pr', hpr', -, hprl⟩ := okOf (alloc.vec.from_elem_spec _ _ (UScalar.cast .Usize t.height) hclone)
  rw [hpr'] at hpr; obtain rfl := Result.ok_injective hpr
  obtain ⟨⟨a1, root1, proof1⟩, hlp, h⟩ := bindOk h
  have hloop := appendLoop_ok H hp z hzb hZ t.next_index.val (toF leaf, subtreesF t.subtrees)
    { start := 0#usize, «end» := UScalar.cast .Usize t.height } t.subtrees
    (UScalar.cast .Usize t.next_index) leaf pr' _ (by simp) hhu (by simp [hciv])
    (by rw [hprl, hhu]) hsub hleaf rfl hlp
  simp only at hloop
  -- next_index + 1
  obtain ⟨o, ho, h⟩ := bindOk h
  cases hval : t.next_index.checked_add 1#u64 with
  | none =>
    have : o = none := by rw [← hval]; exact (Result.ok_injective ho).symm
    subst this
    have h := okOr_none _ _ h
    obtain ⟨r2, hr2, h⟩ := bindOk h
    have := Result.ok_injective h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
    rw [← hr2] at this; simp at this
  | some val =>
  have : o = some val := by rw [← hval]; exact (Result.ok_injective ho).symm
  subst this
  have h := okOr_some _ _ _ h
  have hv : val.val = t.next_index.val + 1 := by
    have hs := U64.checked_add_bv_spec t.next_index 1#u64; rw [hval] at hs; simpa using hs.2.1
  obtain ⟨ri, hri, h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.root_index = ri := Result.ok_injective hri
  have hriu : (UScalar.cast .Usize t.root_index).val = t.root_index.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := usize_big; omega)
  obtain ⟨o1, ho1, h⟩ := bindOk h
  cases hval1 : Usize.checked_add (UScalar.cast .Usize t.root_index) 1#usize with
  | none =>
    have : o1 = none := by rw [← hval1]; exact (Result.ok_injective ho1).symm
    subst this
    have h := okOr_none _ _ h
    obtain ⟨r2, hr2, h⟩ := bindOk h
    have := Result.ok_injective h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
    rw [← hr2] at this; simp at this
  | some val1 =>
  have : o1 = some val1 := by rw [← hval1]; exact (Result.ok_injective ho1).symm
  subst this
  have h := okOr_some _ _ _ h
  have hv1 : val1.val = t.root_index.val + 1 := by
    have hs := Usize.checked_add_bv_spec (UScalar.cast .Usize t.root_index) 1#usize
    rw [hval1] at hs; rw [hs.2.1, hriu]; simp
  obtain ⟨nri, hnri, h⟩ := bindOk h
  obtain ⟨nri', hnri', hnriv'⟩ := okOf (UScalar.rem_spec val1 (y := UScalar.cast .Usize t.root_history_size)
    (by rw [hsu]; norm_num))
  rw [hnri'] at hnri; obtain rfl := Result.ok_injective hnri
  have hnriv : nri'.val = (t.root_index.val + 1) % 100 := by rw [hnriv', hv1, hsu]
  have hnri100 : nri'.val < 100 := by rw [hnriv]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨i1, hi1, h⟩ := bindOk h
  obtain rfl : UScalar.cast .U64 nri' = i1 := Result.ok_injective hi1
  obtain ⟨a2, ha2, h⟩ := bindOk h
  obtain ⟨a2', ha2', ha2v⟩ := okOf (Std.Array.update_spec t.root_history nri' root1 (by simp; omega))
  rw [ha2'] at ha2; obtain rfl := Result.ok_injective ha2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  have hi1v : (UScalar.cast .U64 nri').val = nri'.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simp; omega)
  refine ⟨?_, ⟨hheight, hsize, by show (UScalar.cast .U64 nri').val < 100; omega⟩, hroomV,
    hv, rfl, rfl, rfl⟩
  have hidxF : (⟨nri'.val, hnri100⟩ : Fin 100) = (toTree t).rootIndex + 1 := by
    apply Fin.ext
    simp only [toTree, Fin.val_add, Fin.val_ofNat, hnriv]
    rw [Nat.mod_eq_of_lt hidx]; rfl
  rw [appendEffectsFold]
  have hinit : ((toF leaf, (toTree t).subtrees) : Spec.F × (Fin 26 → Spec.F))
      = (toF leaf, subtreesF t.subtrees) := rfl
  rw [hinit, show (toTree t).nextIndex = t.next_index.val from rfl, ← hloop]
  simp only [toTree]
  congr 1
  · rw [ha2v, histF_set _ _ _ hnri100, hidxF]; rfl
  · apply Fin.ext
    simp only [Fin.val_add, Fin.val_ofNat, hi1v, hnriv]
    rw [Nat.mod_eq_of_lt hidx]
    simp


omit [Spec.PoseidonHashes] in
/-- A successful `append` keeps the tree's shape (no hash assumption needed). -/
theorem append_shape (H : merkle_tree.Hasher Unit)
    (leaf : Std.Array U8 32#usize) (t t' : merkle_tree.MerkleTreeAccount)
    (p : alloc.vec.Vec (Std.Array U8 32#usize)) (hshape : TreeShape t)
    (h : merkle_tree.append H leaf t = ok (.Ok p, t')) :
    TreeShape t' ∧
      t.next_index.val < 2 ^ 26 ∧ t'.next_index.val = t.next_index.val + 1 ∧
      t'.authority = t.authority ∧ t'.max_deposit_amount = t.max_deposit_amount ∧
      t'.bump = t.bump := by
  obtain ⟨hheight, hsize, hidx⟩ := hshape
  unfold merkle_tree.append at h
  have hhu : (UScalar.cast .Usize t.height).val = 26 := by simp [hheight]
  have hsu : (UScalar.cast .Usize t.root_history_size).val = 100 := by simp [hsize]
  obtain ⟨hu, hhu', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.height = hu := Result.ok_injective hhu'
  obtain ⟨rs, hrs', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.root_history_size = rs := Result.ok_injective hrs'
  obtain ⟨mc, hmc, h⟩ := bindOk h
  obtain ⟨mc', hmc', hmcv, -⟩ := okOf (UScalar.ShiftLeft_spec 1#u64 (UScalar.cast .Usize t.height)
    (2 ^ 64) (by rw [hhu]; decide) (by simp [U64.size, U64.numBits]))
  rw [hmc'] at hmc; obtain rfl := Result.ok_injective hmc
  have hmcV : mc'.val = 2 ^ 26 := by rw [hmcv, hhu]; decide
  by_cases hroom : t.next_index < mc'
  swap
  · rw [if_neg hroom] at h
    have := Result.ok_injective h; simp at this
  rw [if_pos hroom] at h
  have hroomV : t.next_index.val < 2 ^ 26 := by rw [← hmcV]; exact hroom
  have hciv : (UScalar.cast .Usize t.next_index).val = t.next_index.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := usize_big; omega)
  obtain ⟨ci, hci', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.next_index = ci := Result.ok_injective hci'
  obtain ⟨pr, hpr, h⟩ := bindOk h
  have hclone : (core.clone.CloneArray 32#usize core.clone.CloneU8).clone (Std.Array.repeat 32#usize 0#u8)
      = ok (Std.Array.repeat 32#usize 0#u8) := by
    obtain ⟨a', ha', heq⟩ := okOf (core.array.CloneArray.clone_spec core.clone.CloneU8
      (Std.Array.repeat 32#usize 0#u8) (by intro x _; rfl))
    show core.array.CloneArray.clone core.clone.CloneU8 _ = _
    rw [ha', ← heq]
  obtain ⟨pr', hpr', -, hprl⟩ := okOf (alloc.vec.from_elem_spec _ _ (UScalar.cast .Usize t.height) hclone)
  rw [hpr'] at hpr; obtain rfl := Result.ok_injective hpr
  obtain ⟨⟨a1, root1, proof1⟩, hlp, h⟩ := bindOk h
  -- next_index + 1
  obtain ⟨o, ho, h⟩ := bindOk h
  cases hval : t.next_index.checked_add 1#u64 with
  | none =>
    have : o = none := by rw [← hval]; exact (Result.ok_injective ho).symm
    subst this
    have h := okOr_none _ _ h
    obtain ⟨r2, hr2, h⟩ := bindOk h
    have := Result.ok_injective h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
    rw [← hr2] at this; simp at this
  | some val =>
  have : o = some val := by rw [← hval]; exact (Result.ok_injective ho).symm
  subst this
  have h := okOr_some _ _ _ h
  have hv : val.val = t.next_index.val + 1 := by
    have hs := U64.checked_add_bv_spec t.next_index 1#u64; rw [hval] at hs; simpa using hs.2.1
  obtain ⟨ri, hri, h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.root_index = ri := Result.ok_injective hri
  have hriu : (UScalar.cast .Usize t.root_index).val = t.root_index.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := usize_big; omega)
  obtain ⟨o1, ho1, h⟩ := bindOk h
  cases hval1 : Usize.checked_add (UScalar.cast .Usize t.root_index) 1#usize with
  | none =>
    have : o1 = none := by rw [← hval1]; exact (Result.ok_injective ho1).symm
    subst this
    have h := okOr_none _ _ h
    obtain ⟨r2, hr2, h⟩ := bindOk h
    have := Result.ok_injective h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
    rw [← hr2] at this; simp at this
  | some val1 =>
  have : o1 = some val1 := by rw [← hval1]; exact (Result.ok_injective ho1).symm
  subst this
  have h := okOr_some _ _ _ h
  have hv1 : val1.val = t.root_index.val + 1 := by
    have hs := Usize.checked_add_bv_spec (UScalar.cast .Usize t.root_index) 1#usize
    rw [hval1] at hs; rw [hs.2.1, hriu]; simp
  obtain ⟨nri, hnri, h⟩ := bindOk h
  obtain ⟨nri', hnri', hnriv'⟩ := okOf (UScalar.rem_spec val1 (y := UScalar.cast .Usize t.root_history_size)
    (by rw [hsu]; norm_num))
  rw [hnri'] at hnri; obtain rfl := Result.ok_injective hnri
  have hnriv : nri'.val = (t.root_index.val + 1) % 100 := by rw [hnriv', hv1, hsu]
  have hnri100 : nri'.val < 100 := by rw [hnriv]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨i1, hi1, h⟩ := bindOk h
  obtain rfl : UScalar.cast .U64 nri' = i1 := Result.ok_injective hi1
  obtain ⟨a2, ha2, h⟩ := bindOk h
  obtain ⟨a2', ha2', ha2v⟩ := okOf (Std.Array.update_spec t.root_history nri' root1 (by simp; omega))
  rw [ha2'] at ha2; obtain rfl := Result.ok_injective ha2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  have hi1v : (UScalar.cast .U64 nri').val = nri'.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simp; omega)
  exact ⟨⟨hheight, hsize, by show (UScalar.cast .U64 nri').val < 100; omega⟩, hroomV,
    hv, rfl, rfl, rfl⟩

omit [Spec.PoseidonHashes] in
/-- `append`'s loop hashes only canonical values and keeps the subtrees and the running hash
    canonical: it starts from the leaf and the subtrees, hashes them with zero hashes and
    subtrees, and stores only the running hash and subtrees it read. -/
theorem appendLoop_canonical (H : merkle_tree.Hasher Unit)
    (hc : ∀ a b h, Canonical a → Canonical b → H.hash_pair a b = ok h → Canonical h)
    (z : Std.Array (Std.Array U8 32#usize) 41#usize) (hzb : H.zero_bytes = ok z)
    (hzc : ∀ i, i ≤ 26 → Canonical (z.val[i]!))
    (iter : core.ops.range.Range Usize) (a : Std.Array (Std.Array U8 32#usize) 26#usize)
    (ci : Usize) (cur : Std.Array U8 32#usize) (proof : alloc.vec.Vec (Std.Array U8 32#usize))
    (r : (Std.Array (Std.Array U8 32#usize) 26#usize) × (Std.Array U8 32#usize) ×
      (alloc.vec.Vec (Std.Array U8 32#usize)))
    (hend : iter.end.val = 26) (ha : ∀ j, j < 26 → Canonical (a.val[j]!)) (hcur : Canonical cur)
    (h : merkle_tree.append_loop H iter a ci cur proof = ok r) :
    (∀ j, j < 26 → Canonical (r.1.val[j]!)) ∧ Canonical r.2.1 := by
  unfold merkle_tree.append_loop at h
  refine loop_ok_induction _
    (fun x : (core.ops.range.Range Usize) × (Std.Array (Std.Array U8 32#usize) 26#usize)
        × Usize × (Std.Array U8 32#usize) × (alloc.vec.Vec (Std.Array U8 32#usize)) =>
      26 - x.1.start.val)
    (fun x => x.1.end.val = 26 ∧ (∀ j, j < 26 → Canonical (x.2.1.val[j]!)) ∧ Canonical x.2.2.2.1)
    (fun r => (∀ j, j < 26 → Canonical (r.1.val[j]!)) ∧ Canonical r.2.1)
    ?_ _ r ⟨hend, ha, hcur⟩ h
  rintro ⟨it, a, ci, cur, proof⟩ rr ⟨hend, ha, hcur⟩ hr
  simp only at hend ha hcur
  unfold merkle_tree.append_loop.body at hr
  simp only [core.iter.range.StepUsize] at hr
  by_cases hlt : it.start.val < 26
  · obtain ⟨⟨o, it1⟩, hn, ho, hs1, he1⟩ := okOf
      (core.iter.range.IteratorRange.next_UScalar_some_spec cloneUsize ltUsize it (by omega))
    rw [hn, bind_tc_ok] at hr
    subst ho
    obtain ⟨⟨sub, back⟩, hix, hr⟩ := bindOk hr
    obtain ⟨⟨sub', back'⟩, hix', hsub, hback⟩ := okOf (Std.Array.index_mut_usize_spec a it.start (by simp; omega))
    rw [hix'] at hix
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hix)
    obtain ⟨z', hz', hr⟩ := bindOk hr
    rw [hzb] at hz'; obtain rfl := Result.ok_injective hz'
    obtain ⟨zb, hzi, hr⟩ := bindOk hr
    obtain ⟨zb', hzi', hzbv⟩ := okOf (Std.Array.index_usize_spec z it.start (by simp; omega))
    rw [hzi'] at hzi; obtain rfl := Result.ok_injective hzi
    obtain ⟨c2, -, hr⟩ := bindOk hr
    obtain ⟨⟨left, right, proof1⟩, hlr, hr⟩ := bindOk hr
    have hlr' : (left = cur ∧ right = zb') ∨ (left = sub' ∧ right = cur) := by
      split at hlr
      · obtain ⟨_, -, hlr⟩ := bindOk hlr
        have := Result.ok_injective hlr; simp only [Prod.mk.injEq] at this
        exact Or.inl ⟨this.1.symm, this.2.1.symm⟩
      · obtain ⟨_, -, hlr⟩ := bindOk hlr
        have := Result.ok_injective hlr; simp only [Prod.mk.injEq] at this
        exact Or.inr ⟨this.1.symm, this.2.1.symm⟩
    have hsubc : Canonical sub' := by
      have := ha it.start.val hlt
      rw [getElem!_pos _ _ (by simp; omega)] at this
      rw [hsub]; exact this
    have hzbc : Canonical zb' := by
      have := hzc it.start.val (by omega)
      rw [getElem!_pos _ _ (by simp; omega)] at this
      rw [hzbv]; exact this
    have hleftc : Canonical left := by
      rcases hlr' with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> assumption
    have hrightc : Canonical right := by
      rcases hlr' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> assumption
    obtain ⟨hv, hhash, hr⟩ := bindOk hr
    obtain ⟨ci', -, hr⟩ := bindOk hr
    have hrr := (Result.ok_injective hr).symm
    subst hrr
    refine ⟨⟨?_, ?_, hc _ _ _ hleftc hrightc hhash⟩, ?_⟩
    · show it1.end.val = 26; rw [he1]; exact hend
    · show ∀ j, j < 26 → Canonical (back' left).val[j]!
      rw [hback]; exact set_canonical _ _ _ hlt ha hleftc
    · show 26 - it1.start.val < 26 - it.start.val; omega
  · obtain ⟨⟨o, it1⟩, hn, ho, hit⟩ := okOf
      (core.iter.range.IteratorRange.next_UScalar_none_spec ltUsize it (by omega))
    rw [hn, bind_tc_ok] at hr
    subst ho
    have hrr := (Result.ok_injective hr).symm
    subst hrr
    exact ⟨ha, hcur⟩

omit [Spec.PoseidonHashes] in
/-- If `append` returns `Ok` and the tree's stored roots are canonical, so are the new tree's:
    the new slot holds the loop's final hash, a Poseidon output. -/
theorem append_history_canonical (H : merkle_tree.Hasher Unit)
    (hc : ∀ a b h, Canonical a → Canonical b → H.hash_pair a b = ok h → Canonical h)
    (z : Std.Array (Std.Array U8 32#usize) 41#usize) (hzb : H.zero_bytes = ok z)
    (hzc : ∀ i, i ≤ 26 → Canonical (z.val[i]!))
    (leaf : Std.Array U8 32#usize) (t t' : merkle_tree.MerkleTreeAccount)
    (p : alloc.vec.Vec (Std.Array U8 32#usize)) (hshape : TreeShape t)
    (hhist : ∀ j : Fin 100, Canonical t.root_history.val[j.val]!)
    (hsub : ∀ j : Fin 26, Canonical t.subtrees.val[j.val]!) (hleaf : Canonical leaf)
    (h : merkle_tree.append H leaf t = ok (.Ok p, t')) :
    ∀ j : Fin 100, Canonical t'.root_history.val[j.val]! := by
  obtain ⟨hheight, hsize, hidx⟩ := hshape
  unfold merkle_tree.append at h
  have hhu : (UScalar.cast .Usize t.height).val = 26 := by simp [hheight]
  have hsu : (UScalar.cast .Usize t.root_history_size).val = 100 := by simp [hsize]
  obtain ⟨hu, hhu', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.height = hu := Result.ok_injective hhu'
  obtain ⟨rs, hrs', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.root_history_size = rs := Result.ok_injective hrs'
  obtain ⟨mc, hmc, h⟩ := bindOk h
  obtain ⟨mc', hmc', hmcv, -⟩ := okOf (UScalar.ShiftLeft_spec 1#u64 (UScalar.cast .Usize t.height)
    (2 ^ 64) (by rw [hhu]; decide) (by simp [U64.size, U64.numBits]))
  rw [hmc'] at hmc; obtain rfl := Result.ok_injective hmc
  have hmcV : mc'.val = 2 ^ 26 := by rw [hmcv, hhu]; decide
  by_cases hroom : t.next_index < mc'
  swap
  · rw [if_neg hroom] at h
    have := Result.ok_injective h; simp at this
  rw [if_pos hroom] at h
  have hroomV : t.next_index.val < 2 ^ 26 := by rw [← hmcV]; exact hroom
  have hciv : (UScalar.cast .Usize t.next_index).val = t.next_index.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := usize_big; omega)
  obtain ⟨ci, hci', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.next_index = ci := Result.ok_injective hci'
  obtain ⟨pr, hpr, h⟩ := bindOk h
  have hclone : (core.clone.CloneArray 32#usize core.clone.CloneU8).clone (Std.Array.repeat 32#usize 0#u8)
      = ok (Std.Array.repeat 32#usize 0#u8) := by
    obtain ⟨a', ha', heq⟩ := okOf (core.array.CloneArray.clone_spec core.clone.CloneU8
      (Std.Array.repeat 32#usize 0#u8) (by intro x _; rfl))
    show core.array.CloneArray.clone core.clone.CloneU8 _ = _
    rw [ha', ← heq]
  obtain ⟨pr', hpr', -, hprl⟩ := okOf (alloc.vec.from_elem_spec _ _ (UScalar.cast .Usize t.height) hclone)
  rw [hpr'] at hpr; obtain rfl := Result.ok_injective hpr
  obtain ⟨⟨a1, root1, proof1⟩, hlp, h⟩ := bindOk h
  -- next_index + 1
  obtain ⟨o, ho, h⟩ := bindOk h
  cases hval : t.next_index.checked_add 1#u64 with
  | none =>
    have : o = none := by rw [← hval]; exact (Result.ok_injective ho).symm
    subst this
    have h := okOr_none _ _ h
    obtain ⟨r2, hr2, h⟩ := bindOk h
    have := Result.ok_injective h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
    rw [← hr2] at this; simp at this
  | some val =>
  have : o = some val := by rw [← hval]; exact (Result.ok_injective ho).symm
  subst this
  have h := okOr_some _ _ _ h
  have hv : val.val = t.next_index.val + 1 := by
    have hs := U64.checked_add_bv_spec t.next_index 1#u64; rw [hval] at hs; simpa using hs.2.1
  obtain ⟨ri, hri, h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.root_index = ri := Result.ok_injective hri
  have hriu : (UScalar.cast .Usize t.root_index).val = t.root_index.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := usize_big; omega)
  obtain ⟨o1, ho1, h⟩ := bindOk h
  cases hval1 : Usize.checked_add (UScalar.cast .Usize t.root_index) 1#usize with
  | none =>
    have : o1 = none := by rw [← hval1]; exact (Result.ok_injective ho1).symm
    subst this
    have h := okOr_none _ _ h
    obtain ⟨r2, hr2, h⟩ := bindOk h
    have := Result.ok_injective h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
    rw [← hr2] at this; simp at this
  | some val1 =>
  have : o1 = some val1 := by rw [← hval1]; exact (Result.ok_injective ho1).symm
  subst this
  have h := okOr_some _ _ _ h
  have hv1 : val1.val = t.root_index.val + 1 := by
    have hs := Usize.checked_add_bv_spec (UScalar.cast .Usize t.root_index) 1#usize
    rw [hval1] at hs; rw [hs.2.1, hriu]; simp
  obtain ⟨nri, hnri, h⟩ := bindOk h
  obtain ⟨nri', hnri', hnriv'⟩ := okOf (UScalar.rem_spec val1 (y := UScalar.cast .Usize t.root_history_size)
    (by rw [hsu]; norm_num))
  rw [hnri'] at hnri; obtain rfl := Result.ok_injective hnri
  have hnriv : nri'.val = (t.root_index.val + 1) % 100 := by rw [hnriv', hv1, hsu]
  have hnri100 : nri'.val < 100 := by rw [hnriv]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨i1, hi1, h⟩ := bindOk h
  obtain rfl : UScalar.cast .U64 nri' = i1 := Result.ok_injective hi1
  obtain ⟨a2, ha2, h⟩ := bindOk h
  obtain ⟨a2', ha2', ha2v⟩ := okOf (Std.Array.update_spec t.root_history nri' root1 (by simp; omega))
  rw [ha2'] at ha2; obtain rfl := Result.ok_injective ha2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  have hroot1 : Canonical root1 :=
    (appendLoop_canonical H hc z hzb hzc _ _ _ _ _ _ (by simpa using hhu)
      (fun i hi => hsub ⟨i, hi⟩) hleaf hlp).2
  intro j
  show Canonical a2'.val[j.val]!
  rw [ha2v]
  have hlen : t.root_history.val.length = 100 := by simp
  simp only [Std.Array.set_val_eq]
  by_cases hj : j.val = nri'.val
  · rw [getElem!_pos _ _ (by simp [hlen])]; simp [hj]; exact hroot1
  · rw [getElem!_pos _ _ (by simp [hlen])]
    have := hhist j
    rw [getElem!_pos _ _ (by simp [hlen])] at this
    simpa [Ne.symm hj] using this

omit [Spec.PoseidonHashes] in
/-- If `append` returns `Ok`, the leaf and the tree's subtrees are canonical, so are the new
    tree's subtrees. -/
theorem append_subtrees_canonical (H : merkle_tree.Hasher Unit)
    (hc : ∀ a b h, Canonical a → Canonical b → H.hash_pair a b = ok h → Canonical h)
    (z : Std.Array (Std.Array U8 32#usize) 41#usize) (hzb : H.zero_bytes = ok z)
    (hzc : ∀ i, i ≤ 26 → Canonical (z.val[i]!))
    (leaf : Std.Array U8 32#usize) (t t' : merkle_tree.MerkleTreeAccount)
    (p : alloc.vec.Vec (Std.Array U8 32#usize)) (hshape : TreeShape t)
    (hsub : ∀ j : Fin 26, Canonical t.subtrees.val[j.val]!) (hleaf : Canonical leaf)
    (h : merkle_tree.append H leaf t = ok (.Ok p, t')) :
    ∀ j : Fin 26, Canonical t'.subtrees.val[j.val]! := by
  obtain ⟨hheight, hsize, hidx⟩ := hshape
  unfold merkle_tree.append at h
  have hhu : (UScalar.cast .Usize t.height).val = 26 := by simp [hheight]
  have hsu : (UScalar.cast .Usize t.root_history_size).val = 100 := by simp [hsize]
  obtain ⟨hu, hhu', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.height = hu := Result.ok_injective hhu'
  obtain ⟨rs, hrs', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.root_history_size = rs := Result.ok_injective hrs'
  obtain ⟨mc, hmc, h⟩ := bindOk h
  obtain ⟨mc', hmc', hmcv, -⟩ := okOf (UScalar.ShiftLeft_spec 1#u64 (UScalar.cast .Usize t.height)
    (2 ^ 64) (by rw [hhu]; decide) (by simp [U64.size, U64.numBits]))
  rw [hmc'] at hmc; obtain rfl := Result.ok_injective hmc
  have hmcV : mc'.val = 2 ^ 26 := by rw [hmcv, hhu]; decide
  by_cases hroom : t.next_index < mc'
  swap
  · rw [if_neg hroom] at h
    have := Result.ok_injective h; simp at this
  rw [if_pos hroom] at h
  have hroomV : t.next_index.val < 2 ^ 26 := by rw [← hmcV]; exact hroom
  have hciv : (UScalar.cast .Usize t.next_index).val = t.next_index.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := usize_big; omega)
  obtain ⟨ci, hci', h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.next_index = ci := Result.ok_injective hci'
  obtain ⟨pr, hpr, h⟩ := bindOk h
  have hclone : (core.clone.CloneArray 32#usize core.clone.CloneU8).clone (Std.Array.repeat 32#usize 0#u8)
      = ok (Std.Array.repeat 32#usize 0#u8) := by
    obtain ⟨a', ha', heq⟩ := okOf (core.array.CloneArray.clone_spec core.clone.CloneU8
      (Std.Array.repeat 32#usize 0#u8) (by intro x _; rfl))
    show core.array.CloneArray.clone core.clone.CloneU8 _ = _
    rw [ha', ← heq]
  obtain ⟨pr', hpr', -, hprl⟩ := okOf (alloc.vec.from_elem_spec _ _ (UScalar.cast .Usize t.height) hclone)
  rw [hpr'] at hpr; obtain rfl := Result.ok_injective hpr
  obtain ⟨⟨a1, root1, proof1⟩, hlp, h⟩ := bindOk h
  -- next_index + 1
  obtain ⟨o, ho, h⟩ := bindOk h
  cases hval : t.next_index.checked_add 1#u64 with
  | none =>
    have : o = none := by rw [← hval]; exact (Result.ok_injective ho).symm
    subst this
    have h := okOr_none _ _ h
    obtain ⟨r2, hr2, h⟩ := bindOk h
    have := Result.ok_injective h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
    rw [← hr2] at this; simp at this
  | some val =>
  have : o = some val := by rw [← hval]; exact (Result.ok_injective ho).symm
  subst this
  have h := okOr_some _ _ _ h
  have hv : val.val = t.next_index.val + 1 := by
    have hs := U64.checked_add_bv_spec t.next_index 1#u64; rw [hval] at hs; simpa using hs.2.1
  obtain ⟨ri, hri, h⟩ := bindOk h
  obtain rfl : UScalar.cast .Usize t.root_index = ri := Result.ok_injective hri
  have hriu : (UScalar.cast .Usize t.root_index).val = t.root_index.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by have := usize_big; omega)
  obtain ⟨o1, ho1, h⟩ := bindOk h
  cases hval1 : Usize.checked_add (UScalar.cast .Usize t.root_index) 1#usize with
  | none =>
    have : o1 = none := by rw [← hval1]; exact (Result.ok_injective ho1).symm
    subst this
    have h := okOr_none _ _ h
    obtain ⟨r2, hr2, h⟩ := bindOk h
    have := Result.ok_injective h
    simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hr2
    rw [← hr2] at this; simp at this
  | some val1 =>
  have : o1 = some val1 := by rw [← hval1]; exact (Result.ok_injective ho1).symm
  subst this
  have h := okOr_some _ _ _ h
  have hv1 : val1.val = t.root_index.val + 1 := by
    have hs := Usize.checked_add_bv_spec (UScalar.cast .Usize t.root_index) 1#usize
    rw [hval1] at hs; rw [hs.2.1, hriu]; simp
  obtain ⟨nri, hnri, h⟩ := bindOk h
  obtain ⟨nri', hnri', hnriv'⟩ := okOf (UScalar.rem_spec val1 (y := UScalar.cast .Usize t.root_history_size)
    (by rw [hsu]; norm_num))
  rw [hnri'] at hnri; obtain rfl := Result.ok_injective hnri
  have hnriv : nri'.val = (t.root_index.val + 1) % 100 := by rw [hnriv', hv1, hsu]
  have hnri100 : nri'.val < 100 := by rw [hnriv]; exact Nat.mod_lt _ (by norm_num)
  obtain ⟨i1, hi1, h⟩ := bindOk h
  obtain rfl : UScalar.cast .U64 nri' = i1 := Result.ok_injective hi1
  obtain ⟨a2, ha2, h⟩ := bindOk h
  obtain ⟨a2', ha2', ha2v⟩ := okOf (Std.Array.update_spec t.root_history nri' root1 (by simp; omega))
  rw [ha2'] at ha2; obtain rfl := Result.ok_injective ha2
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Result.ok_injective h)
  intro j
  exact (appendLoop_canonical H hc z hzb hzc _ _ _ _ _ _ (by simpa using hhu)
    (fun i hi => hsub ⟨i, hi⟩) hleaf hlp).1 j.val j.isLt

omit [Spec.PoseidonHashes] in
/-- `initialize`'s loop writes zero hashes `0 … 25` into the subtrees: canonical if they are. -/
theorem initLoop_subtrees (iter : core.ops.range.Range Usize)
    (a : Std.Array (Std.Array U8 32#usize) 26#usize) (z : Std.Array (Std.Array U8 32#usize) 41#usize)
    (r : Std.Array (Std.Array U8 32#usize) 26#usize)
    (hzc : ∀ i, i ≤ 26 → Canonical (z.val[i]!)) (hend : iter.end.val = 26)
    (ha : ∀ j, j < 26 → Canonical (a.val[j]!))
    (h : merkle_tree.initialize_loop iter a z = ok r) :
    ∀ j, j < 26 → Canonical (r.val[j]!) := by
  unfold merkle_tree.initialize_loop at h
  refine loop_ok_induction _
    (fun x : (core.ops.range.Range Usize) × (Std.Array (Std.Array U8 32#usize) 26#usize) =>
      26 - x.1.start.val)
    (fun x => x.1.end.val = 26 ∧ ∀ j, j < 26 → Canonical (x.2.val[j]!))
    (fun r => ∀ j, j < 26 → Canonical (r.val[j]!))
    ?_ _ r ⟨hend, ha⟩ h
  rintro ⟨it, a⟩ rr ⟨hend, ha⟩ hr
  simp only at hend ha
  unfold merkle_tree.initialize_loop.body at hr
  simp only [core.iter.range.StepUsize] at hr
  by_cases hlt : it.start.val < 26
  · obtain ⟨⟨o, it1⟩, hn, ho, hs1, he1⟩ := okOf
      (core.iter.range.IteratorRange.next_UScalar_some_spec cloneUsize ltUsize it (by omega))
    rw [hn, bind_tc_ok] at hr
    subst ho
    obtain ⟨zb, hzi, hr⟩ := bindOk hr
    obtain ⟨zb', hzi', hzbv⟩ := okOf (Std.Array.index_usize_spec z it.start (by simp; omega))
    rw [hzi'] at hzi; obtain rfl := Result.ok_injective hzi
    obtain ⟨a2, ha2, hr⟩ := bindOk hr
    obtain ⟨a2', ha2', ha2v⟩ := okOf (Std.Array.update_spec a it.start zb' (by simp; omega))
    rw [ha2'] at ha2; obtain rfl := Result.ok_injective ha2
    have hrr := (Result.ok_injective hr).symm
    subst hrr
    have hzc' : Canonical zb' := by
      have := hzc it.start.val (by omega)
      rw [getElem!_pos _ _ (by simp; omega)] at this
      rw [hzbv]; exact this
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show it1.end.val = 26; rw [he1]; exact hend
    · show ∀ j, j < 26 → Canonical a2'.val[j]!
      intro j hj
      rw [ha2v]
      simp only [Std.Array.set_val_eq]
      by_cases hji : j = it.start.val
      · rw [getElem!_pos _ _ (by simp; omega)]; simp [hji]; exact hzc'
      · rw [getElem!_pos _ _ (by simp; omega)]
        have := ha j hj
        rw [getElem!_pos _ _ (by simp; omega)] at this
        have hne : it.start.val ≠ j := Ne.symm hji
        simpa [hne] using this
    · show 26 - it1.start.val < 26 - it.start.val; omega
  · obtain ⟨⟨o, it1⟩, hn, ho, hit⟩ := okOf
      (core.iter.range.IteratorRange.next_UScalar_none_spec ltUsize it (by omega))
    rw [hn, bind_tc_ok] at hr
    subst ho
    have hrr := (Result.ok_injective hr).symm
    subst hrr
    exact ha

omit [Spec.PoseidonHashes] in
/-- With no room, `append` returns `MerkleTreeFull` and leaves the tree as it was. -/
theorem append_full (H : merkle_tree.Hasher Unit) (leaf : Std.Array U8 32#usize)
    (t : merkle_tree.MerkleTreeAccount) (hheight : t.height.val = 26)
    (hfull : 2 ^ 26 ≤ t.next_index.val) :
    merkle_tree.append H leaf t = ok (.Err error.ErrorCode.MerkleTreeFull, t) := by
  have hhu : (UScalar.cast .Usize t.height).val = 26 := by simp [hheight]
  obtain ⟨mc', hmc', hmcv, -⟩ := okOf (UScalar.ShiftLeft_spec 1#u64 (UScalar.cast .Usize t.height)
    (2 ^ 64) (by rw [hhu]; decide) (by simp [U64.size, U64.numBits]))
  have hmcV : mc'.val = 2 ^ 26 := by rw [hmcv, hhu]; decide
  have hno : ¬ t.next_index < mc' := by
    intro h; have : t.next_index.val < mc'.val := h; omega
  unfold merkle_tree.append
  simp only [lift, bind_tc_ok]
  rw [hmc', bind_tc_ok, if_neg hno]

/-- Poseidon of canonical inputs is canonical (`HashesAgree.poseidon`). -/
theorem HashesAgree.poseidon_canonical [Spec.Sha] {d : Deployment}
    (hashes : HashesAgree d) :
    ∀ a b h, Canonical a → Canonical b → d.crypto.hasher.hash_pair a b = ok h → Canonical h :=
  fun a b h ha hb hh => (hashes.poseidon a b h ha hb hh).1

/-- The zero hashes are canonical (`HashesAgree.zeroBytes`). -/
theorem HashesAgree.zeroBytes_canonical [Spec.Sha] {d : Deployment}
    (hashes : HashesAgree d) :
    ∃ z, d.crypto.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → Canonical (z.val[i]!) := by
  obtain ⟨z, hzb, hZ⟩ := hashes.zeroBytes
  exact ⟨z, hzb, fun i hi => (hZ i hi).1⟩

/-- The zero hashes are the spec's empty-subtree roots (`HashesAgree.zeroBytes`). -/
theorem HashesAgree.zeroBytes_agree [Spec.Sha] {d : Deployment}
    (hashes : HashesAgree d) :
    ∃ z, d.crypto.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = Spec.Z i := by
  obtain ⟨z, hzb, hZ⟩ := hashes.zeroBytes
  exact ⟨z, hzb, fun i hi => (hZ i hi).2⟩

/-- `append_ok` with the hash assumptions of `HashesAgree`, for a canonical leaf and canonical
    subtrees. -/
theorem append_ok' [Spec.Sha] (d : Deployment) (hashes : HashesAgree d) (leaf : Std.Array U8 32#usize)
    (t t' : merkle_tree.MerkleTreeAccount) (p : alloc.vec.Vec (Std.Array U8 32#usize))
    (hshape : TreeShape t) (hsub : ∀ j : Fin 26, Canonical t.subtrees.val[j.val]!)
    (hleaf : Canonical leaf) (h : merkle_tree.append d.crypto.hasher leaf t = ok (.Ok p, t')) :
    toTree t' = Spec.appendEffects (toF leaf) (toTree t) ∧ TreeShape t' ∧
      t.next_index.val < 2 ^ 26 ∧ t'.next_index.val = t.next_index.val + 1 ∧
      t'.authority = t.authority ∧ t'.max_deposit_amount = t.max_deposit_amount ∧
      t'.bump = t.bump := by
  obtain ⟨z, hzb, hZ⟩ := hashes.zeroBytes
  exact append_ok d.crypto.hasher hashes.poseidon z hzb hZ leaf t t' p hshape
    (fun i hi => hsub ⟨i, hi⟩) hleaf h

/-- `append_subtrees_canonical` with the hash assumptions of `HashesAgree`. -/
theorem append_subtrees_canonical' [Spec.Sha] (d : Deployment) (hashes : HashesAgree d)
    (leaf : Std.Array U8 32#usize) (t t' : merkle_tree.MerkleTreeAccount)
    (p : alloc.vec.Vec (Std.Array U8 32#usize)) (hshape : TreeShape t)
    (hsub : ∀ j : Fin 26, Canonical t.subtrees.val[j.val]!) (hleaf : Canonical leaf)
    (h : merkle_tree.append d.crypto.hasher leaf t = ok (.Ok p, t')) :
    ∀ j : Fin 26, Canonical t'.subtrees.val[j.val]! := by
  obtain ⟨z, hzb, hzc⟩ := hashes.zeroBytes_canonical
  exact append_subtrees_canonical _ hashes.poseidon_canonical z hzb hzc leaf t t' p hshape hsub hleaf h

end Connection
