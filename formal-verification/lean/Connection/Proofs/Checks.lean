import Connection.Mapping
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs of the connection theorems for the program's checks

NOT FOR REVIEW: the statements are restated in `Connection/ConnectionTheorems.lean`. Ported from the
connection to the earlier `fv_*` model (commit e862db8, `Connection/Basic.lean`); the
extracted Rust is the same, only names and the Aeneas version changed.
-/

namespace Connection

/-! ## `check_public_amount` ↔ `pubAmtConsistent` -/

/-- `(n : Fr).val = n` for `n` below the modulus. -/
private theorem val_natCast_small {n : ℕ} (h : n < 2 ^ 64) : (n : Fr).val = n :=
  ZMod.val_natCast_of_lt (lt_of_lt_of_le h (by decide))

private theorem checkPublicAmount_iff (extAmount : I64) (fee : U64) (pa : Std.Array U8 32#usize) :
    ∃ b, zkcash_core.utils.check_public_amount arkFr extAmount fee pa = ok b ∧
      (b = true ↔ LeanSpec.pubAmtConsistent extAmount.val fee.val (toF pa) ∧ LeanSpec.amountsInRange extAmount.val fee.val ∧
        extAmount.val ≠ 0) := by
  have hlo : -2 ^ 63 ≤ extAmount.val := by scalar_tac
  have hhi : extAmount.val < 2 ^ 63 := by scalar_tac
  have hfee : fee.val < 2 ^ 64 := by scalar_tac
  unfold zkcash_core.utils.check_public_amount
  simp only [arkFr, lift, bind_tc_ok]
  by_cases hmin : extAmount = core.num.I64.MIN
  · have hv : extAmount.val = -9223372036854775808 := by rw [hmin]; rfl
    refine ⟨false, by simp [hmin], ?_⟩
    simp [LeanSpec.amountsInRange, hv]
  · have hv : extAmount.val ≠ -9223372036854775808 := by
      intro h; apply hmin; rw [IScalar.eq_equiv, h]; rfl
    by_cases hpos : extAmount ≥ 0#i64
    · have hpos' : 0 ≤ extAmount.val := by scalar_tac
      have hc : (IScalar.hcast UScalarTy.U64 extAmount).val = extAmount.val.toNat := by
        rw [IScalar.hcast_val_eq]; congr 1; exact Int.emod_eq_of_lt hpos' (by simp; omega)
      simp only [hmin, hpos, if_false, if_true]
      rw [val_natCast_small (by rw [hc]; omega), val_natCast_small hfee, hc]
      by_cases hle : extAmount.val.toNat ≤ fee.val
      · refine ⟨false, by simp [hle], ?_⟩
        simp only [Bool.false_eq_true, false_iff]
        rintro ⟨hp, -, h0⟩; have := hp.1 (by omega); omega
      · refine ⟨_, by simp [hle]; rfl, ?_⟩
        simp only [decide_eq_true_eq, LeanSpec.pubAmtConsistent, toF]
        have e : ((extAmount.val.toNat : ℕ) : Fr) = (extAmount.val : Fr) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hpos']
        constructor
        · intro h; refine ⟨⟨fun _ => by omega, ?_⟩, by simp only [LeanSpec.amountsInRange]; omega, by omega⟩
          show ((beNat pa : ℕ) : Fr) = (extAmount.val : Fr) - ((fee.val : ℕ) : Fr)
          rw [← h, e]
        · rintro ⟨⟨-, h⟩, -, -⟩
          show ((extAmount.val.toNat : ℕ) : Fr) - ((fee.val : ℕ) : Fr) = ((beNat pa : ℕ) : Fr)
          rw [e]; exact h.symm
    · have hneg : extAmount.val < 0 := by scalar_tac
      -- `checked_neg` returns `-extAmount`, since `extAmount` is not `i64::MIN`
      obtain ⟨v, hvok, hvv⟩ : ∃ v, IScalar.neg extAmount = ok v ∧ v.val = -extAmount.val := by
        have := IScalar.neg_step extAmount (by
          intro h; apply hv; rw [h]; simp [I64.min_eq])
        cases hr : IScalar.neg extAmount <;> simp_all
      have hc : (IScalar.hcast UScalarTy.U64 v).val = (-extAmount.val).toNat := by
        rw [IScalar.hcast_val_eq, hvv]; congr 1; exact Int.emod_eq_of_lt (by omega) (by simp; omega)
      simp only [hmin, hpos, if_false, core.num.I64.checked_neg, hvok, Option.ofResult, bind_tc_ok]
      refine ⟨_, rfl, ?_⟩
      simp only [decide_eq_true_eq, LeanSpec.pubAmtConsistent, toF]
      have e : (((IScalar.hcast UScalarTy.U64 v).val : ℕ) : Fr) = -(extAmount.val : Fr) := by
        rw [hc, ← Int.cast_natCast, Int.toNat_of_nonneg (by omega), Int.cast_neg]
      constructor
      · intro h; refine ⟨⟨fun h' => absurd h' (by omega), ?_⟩, by simp only [LeanSpec.amountsInRange]; omega, by omega⟩
        show ((beNat pa : ℕ) : Fr) = (extAmount.val : Fr) - ((fee.val : ℕ) : Fr)
        rw [← h, e]; ring
      · rintro ⟨⟨-, h⟩, -, -⟩
        show -((((IScalar.hcast UScalarTy.U64 v).val : ℕ) : Fr) + ((fee.val : ℕ) : Fr)) = ((beNat pa : ℕ) : Fr)
        have h' : ((beNat pa : ℕ) : Fr) = (extAmount.val : Fr) - ((fee.val : ℕ) : Fr) := h
        rw [e, h']; ring
theorem checkPublicAmount_eq (extAmount : I64) (fee : U64) (pa : Std.Array U8 32#usize) :
    zkcash_core.utils.check_public_amount arkFr extAmount fee pa
      = ok (decide (LeanSpec.pubAmtConsistent extAmount.val fee.val (toF pa) ∧ LeanSpec.amountsInRange extAmount.val fee.val ∧
        extAmount.val ≠ 0)) := by
  obtain ⟨b, hb, hiff⟩ := checkPublicAmount_iff extAmount fee pa
  rw [hb]; cases b <;> simp_all <;> exact hiff

/-- Thirty-two zero bytes: the public amount 0. -/
def zeroBytes : Std.Array U8 32#usize := Std.Array.repeat 32#usize 0#u8

theorem checkPublicAmount_L1 :
    zkcash_core.utils.check_public_amount arkFr 0#i64 0#u64 zeroBytes = ok false ∧
      LeanSpec.pubAmtConsistent (0#i64).val (0#u64).val (toF zeroBytes) ∧
        LeanSpec.amountsInRange (0#i64).val (0#u64).val := by
  have hb : beNat zeroBytes = 0 := by rfl
  have hz : toF zeroBytes = 0 := by simp only [toF, hb, Nat.cast_zero]
  refine ⟨?_, ?_⟩
  · rw [checkPublicAmount_eq]; simp
  · simp [LeanSpec.pubAmtConsistent, LeanSpec.amountsInRange, hz]

theorem checkPublicAmount_not_square :
    ¬ ∀ (extAmount : I64) (fee : U64) (pa : Std.Array U8 32#usize),
      zkcash_core.utils.check_public_amount arkFr extAmount fee pa
        = ok (decide (LeanSpec.pubAmtConsistent extAmount.val fee.val (toF pa) ∧ LeanSpec.amountsInRange extAmount.val fee.val)) := by
  intro h
  obtain ⟨h1, h2⟩ := checkPublicAmount_L1
  have := (h 0#i64 0#u64 zeroBytes).symm.trans h1
  rw [decide_eq_true h2] at this
  exact absurd (Result.ok_injective this) (by decide)


/-! ## `is_known_root` ↔ `rootKnown` -/

/-- `PartialEqArray.eq` on bytes is array equality (via Aeneas's slice lemma). -/
theorem arrayEqU8Spec {N : Std.Usize} (a0 a1 : Std.Array U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a0 a1 ⦃ (b : Bool) =>
      b = true ↔ a0 = a1 ⦄ := by
  have heq : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a0 a1
      = core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a0.to_slice a1.to_slice := by
    unfold core.array.equality.PartialEqArray.eq core.slice.cmp.PartialEqSlice.eq
    simp [Array.val_to_slice]
  rw [heq]
  have hne : ∀ x y : U8, core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ ¬ (x = y) ⦄ := by
    intro x y
    simp [core.cmp.impls.PartialEqU8.ne, liftFun2]
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8
    a0.to_slice a1.to_slice hne)
  intro b hb
  constructor
  · intro hbt
    have h := hb.mp hbt
    rw [Slice.eq_iff, Array.val_to_slice, Array.val_to_slice] at h
    exact (Std.Array.eq_iff _ _).mpr h
  · intro h
    apply hb.mpr
    rw [Slice.eq_iff, Array.val_to_slice, Array.val_to_slice]
    exact (Std.Array.eq_iff _ _).mp h

/-- Backward circular distance from `start` to `idx` (both `< 100`). -/
private def backDist (start idx : ℕ) : ℕ := (100 + start - idx) % 100

private theorem getElemBang {α} [Inhabited α] (l : List α) (i : ℕ) (h : i < l.length) :
    l[i]'h = l[i]! := (getElem!_pos l i h).symm

/-- The loop, started at `cur`, accepts exactly when some history slot matches. -/
private theorem isKnownRootLoopSpec
    (a : Std.Array (Std.Array U8 32#usize) 100#usize) (root : Std.Array U8 32#usize)
    (currentRootIndex cur : Std.Usize)
    (hcri : currentRootIndex.val < 100) (hcur : cur.val < 100)
    (hpre : ∀ j : Fin 100,
      backDist currentRootIndex.val j.val < backDist currentRootIndex.val cur.val →
      a.val[j.val]! ≠ root) :
    zkcash_core.merkle_tree.is_known_root_loop a root 100#usize currentRootIndex cur
      ⦃ (ok : Bool) => ok = true ↔ ∃ j : Fin 100, a.val[j.val]! = root ⦄ := by
  unfold zkcash_core.merkle_tree.is_known_root_loop
  apply loop.spec_decr_nat
    (measure := fun x : Std.Usize => 100 - backDist currentRootIndex.val x.val)
    (inv := fun x : Std.Usize => x.val < 100 ∧
      ∀ j : Fin 100, backDist currentRootIndex.val j.val < backDist currentRootIndex.val x.val →
        a.val[j.val]! ≠ root)
  · rintro x ⟨hx, hinv⟩
    unfold zkcash_core.merkle_tree.is_known_root_loop.body
    apply WP.spec_bind (Array.index_usize_spec a x (by scalar_tac))
    intro a1 ha1
    have ha1' : a1 = a.val[x.val]! := ha1.trans (getElemBang a.val x.val (by scalar_tac))
    apply WP.spec_bind (arrayEqU8Spec root a1)
    intro b hb
    by_cases hbv : b = true
    · simp only [hbv, ↓reduceIte, WP.spec_ok, true_iff]
      exact ⟨⟨x.val, hx⟩, by rw [← ha1']; exact (hb.mp hbv).symm⟩
    · have hbf : b = false := by cases b <;> simp_all
      have hne : a.val[x.val]! ≠ root := by rw [← ha1']; exact fun h => hbv (hb.mpr h.symm)
      have hinv' : ∀ j : Fin 100,
          backDist currentRootIndex.val j.val ≤ backDist currentRootIndex.val x.val →
          a.val[j.val]! ≠ root := by
        intro j hj
        rcases lt_or_eq_of_le hj with hlt | heqd
        · exact hinv j hlt
        · have hjx : j.val = x.val := by
            have hbx : backDist currentRootIndex.val x.val < 100 := by
              simp only [backDist]; scalar_tac
            have hbj : backDist currentRootIndex.val j.val < 100 := by
              simp only [backDist]; scalar_tac
            simp only [backDist] at heqd
            omega
          rw [hjx]; exact hne
      simp only [hbf, Bool.false_eq_true, if_false]
      by_cases hx0 : x = 0#usize
      · simp only [hx0, ↓reduceIte]
        apply WP.spec_bind (UScalar.sub_spec (x := (100#usize : Std.Usize)) (y := 1#usize) (by scalar_tac))
        intro i2 hi2
        obtain ⟨hi2val0, -⟩ := hi2
        have hi2val : i2.val = 99 := by scalar_tac
        have hxval : x.val = 0 := by scalar_tac
        by_cases hwrap : i2 = currentRootIndex
        · simp only [hwrap, ↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff, not_exists]
          intro j
          apply hinv'
          have hcri99 : currentRootIndex.val = 99 := by scalar_tac
          simp only [backDist]; scalar_tac
        · simp only [hwrap, ↓reduceIte, WP.spec_ok]
          refine ⟨⟨by scalar_tac, fun j hj => hinv' j ?_⟩, ?_⟩
          · simp only [backDist] at hj ⊢; scalar_tac
          · simp only [backDist]; scalar_tac
      · simp only [hx0, ↓reduceIte]
        apply WP.spec_bind (UScalar.sub_spec (x := x) (y := (1#usize : Std.Usize)) (by scalar_tac))
        intro i2 hi2
        obtain ⟨hi2val, -⟩ := hi2
        by_cases hwrap : i2 = currentRootIndex
        · simp only [hwrap, ↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff, not_exists]
          intro j
          apply hinv'
          have hcri : currentRootIndex.val = x.val - 1 := by scalar_tac
          simp only [backDist]; scalar_tac
        · simp only [hwrap, ↓reduceIte, WP.spec_ok]
          refine ⟨⟨by scalar_tac, fun j hj => hinv' j ?_⟩, ?_⟩
          · simp only [backDist] at hj ⊢; scalar_tac
          · simp only [backDist]; scalar_tac
  · exact ⟨hcur, hpre⟩

private theorem foldlEq (c : ℕ) (l : List U8) :
    l.foldl (fun acc x => acc * 256 + x.val) c
      = c * 256 ^ l.length + l.foldl (fun acc x => acc * 256 + x.val) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (c * 256 + x.val), ih x.val]
    ring

private theorem foldlBound (l : List U8) :
    l.foldl (fun acc x => acc * 256 + x.val) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, pow_succ, Nat.zero_mul, Nat.zero_add]
    rw [foldlEq x.val xs]
    have hx : x.val < 256 := by scalar_tac
    nlinarith [ih, hx]

private theorem mulAddCancel {m x1 x2 r1 r2 : ℕ} (hm : 0 < m) (hr1 : r1 < m) (hr2 : r2 < m)
    (h : x1 * m + r1 = x2 * m + r2) : x1 = x2 ∧ r1 = r2 := by
  have e1 : r1 + m * x1 = r2 + m * x2 := by rw [mul_comm x1, mul_comm x2] at h; omega
  have d1 : (r1 + m * x1) / m = x1 := by
    rw [Nat.add_mul_div_left r1 x1 hm, Nat.div_eq_of_lt hr1, Nat.zero_add]
  have d2 : (r2 + m * x2) / m = x2 := by
    rw [Nat.add_mul_div_left r2 x2 hm, Nat.div_eq_of_lt hr2, Nat.zero_add]
  have hx : x1 = x2 := by rw [← d1, ← d2, e1]
  exact ⟨hx, by rw [hx] at h; omega⟩

/-- Reading equally long byte lists as big-endian numbers is injective. -/
private theorem beListInj : ∀ {l1 l2 : List U8}, l1.length = l2.length →
    l1.foldl (fun acc x => acc * 256 + x.val) 0 = l2.foldl (fun acc x => acc * 256 + x.val) 0 →
    l1 = l2
  | [], [], _, _ => rfl
  | _ :: _, [], hlen, _ => by simp at hlen
  | [], _ :: _, hlen, _ => by simp at hlen
  | x1 :: xs1, x2 :: xs2, hlen, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add] at h
    rw [foldlEq x1.val xs1, foldlEq x2.val xs2, hlen] at h
    obtain ⟨hxeq, hreq⟩ := mulAddCancel (pow_pos (by norm_num) xs2.length)
      (hlen ▸ foldlBound xs1) (foldlBound xs2) h
    have hx : x1 = x2 := by scalar_tac
    rw [hx, beListInj hlen hreq]

/-- `toF` is injective on canonical bytes. -/
theorem toF_injOn {a b : Std.Array U8 32#usize} (ha : Canonical a) (hb : Canonical b)
    (h : toF a = toF b) : a = b := by
  have hval : beNat a = beNat b := by
    have e1 := ZMod.val_natCast_of_lt (n := bn254ScalarModulus) ha
    have e2 := ZMod.val_natCast_of_lt (n := bn254ScalarModulus) hb
    rw [← e1, ← e2]
    exact congrArg ZMod.val h
  exact (Std.Array.eq_iff _ _).mpr
    (beListInj (by rw [Std.Array.property, Std.Array.property]) (by simpa [beNat] using hval))

/-- The spec's big-endian reading of code bytes is the code's. -/
theorem natOfBE_toBytes (l : List U8) :
    LeanSpec.natOfBE (toBytes l) = l.foldl (fun acc x => acc * 256 + x.val) 0 := by
  unfold LeanSpec.natOfBE toBytes
  rw [List.foldl_map]
  congr 1; funext acc x
  show 256 * acc + x.val = acc * 256 + x.val
  ring

theorem toBytes_length (l : List U8) : (toBytes l).length = l.length := by simp [toBytes]

/-- A 32-byte array, as the spec's bytes: the spec reads the same number (`beNat`). -/
theorem natOfBE_toBytes_arr (b : Std.Array U8 32#usize) :
    LeanSpec.natOfBE (toBytes b.val) = beNat b := natOfBE_toBytes b.val

/-- A 32-byte array is the spec's canonical encoding of `x` exactly when it is canonical and
    `toF` maps it to `x`. -/
theorem canonicalEncoding_iff (b : Std.Array U8 32#usize) (x : LeanSpec.F) :
    LeanSpec.canonicalEncoding (toBytes b.val) x ↔ Canonical b ∧ toF b = x := by
  unfold LeanSpec.canonicalEncoding
  rw [natOfBE_toBytes_arr, toBytes_length, Std.Array.property]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨rfl, h1, h2⟩⟩

/-- The root's bytes are known (byte level) exactly when they are canonical and their field
    element is known. -/
theorem rootBytesKnown_iff (T : LeanSpec.Tree) (b : Std.Array U8 32#usize) :
    LeanSpec.rootBytesKnown T (toBytes b.val) ↔ Canonical b ∧ LeanSpec.rootKnown T (toF b) := by
  unfold LeanSpec.rootBytesKnown
  rw [natOfBE_toBytes_arr, toBytes_length, Std.Array.property]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨rfl, h1, h2⟩⟩

theorem zero_canonical : Canonical (Std.Array.repeat 32#usize 0#u8) := by
  simp [Canonical, beNat, bn254ScalarModulus]

private theorem toF_zero : toF (Std.Array.repeat 32#usize 0#u8) = 0 := by
  simp [toF, beNat]

/-- What `is_known_root` returns, for a well-shaped tree: whether the root is non-zero and in
    the history, compared as bytes. -/
private theorem isKnownRootSpec (t : zkcash_core.merkle_tree.MerkleTreeAccount)
    (root : Std.Array U8 32#usize)
    (hsize : t.root_history_size.val = 100) (hidx : t.root_index.val < 100) :
    zkcash_core.merkle_tree.is_known_root t root ⦃ (ok : Bool) =>
      ok = true ↔ (root ≠ Std.Array.repeat 32#usize 0#u8 ∧
        ∃ j : Fin 100, t.root_history.val[j.val]! = root) ⦄ := by
  unfold zkcash_core.merkle_tree.is_known_root
  apply WP.spec_bind (arrayEqU8Spec root (Std.Array.repeat 32#usize 0#u8))
  intro b hb
  by_cases hbv : b = true
  · simp only [hbv, ↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff, not_and]
    intro h; exact absurd (hb.mp hbv) h
  · have hbf : b = false := by cases b <;> simp_all
    simp only [hbf, Bool.false_eq_true, if_false]
    apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize t.root_history_size (by scalar_tac))
    intro rootHistorySize hrhs
    apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize t.root_index (by scalar_tac))
    intro currentRootIndex hcri
    have hrhs' : rootHistorySize = (100#usize : Std.Usize) := by scalar_tac
    rw [hrhs']
    apply WP.spec_mono (isKnownRootLoopSpec t.root_history root currentRootIndex
      currentRootIndex (by scalar_tac) (by scalar_tac)
      (fun j hj => by simp [backDist] at hj))
    intro ok hok
    rw [hok]
    exact ⟨fun h => ⟨fun h0 => hbv (hb.mpr h0), h⟩, fun h => h.2⟩

theorem isKnownRoot_eq (t : zkcash_core.merkle_tree.MerkleTreeAccount) (root : Std.Array U8 32#usize)
    (hshape : TreeShape t)
    (hhist : ∀ j : Fin 100, Canonical t.root_history.val[j.val]!) :
    zkcash_core.merkle_tree.is_known_root t root
      = ok (decide (LeanSpec.rootBytesKnown (toTree t) (toBytes root.val))) := by
  obtain ⟨b, hb, hiff⟩ := (WP.spec_equiv_exists _ _).mp (isKnownRootSpec t root hshape.2.1 hshape.2.2)
  have key : (root ≠ Std.Array.repeat 32#usize 0#u8 ∧ ∃ j : Fin 100, t.root_history.val[j.val]! = root)
      ↔ LeanSpec.rootBytesKnown (toTree t) (toBytes root.val) := by
    rw [rootBytesKnown_iff]
    simp only [LeanSpec.rootKnown, toTree, Set.mem_range]
    constructor
    · rintro ⟨hne, j, hj⟩
      have hroot : Canonical root := hj ▸ hhist j
      exact ⟨hroot, ⟨j, congrArg toF hj⟩,
        fun h0 => hne (toF_injOn hroot zero_canonical (h0.trans toF_zero.symm))⟩
    · rintro ⟨hroot, ⟨j, hj⟩, hne⟩
      exact ⟨fun h => hne (by rw [h, toF_zero]), j, toF_injOn (hhist j) hroot hj⟩
  have hbd : b = decide (LeanSpec.rootBytesKnown (toTree t) (toBytes root.val)) := by
    have h := hiff.trans key
    cases b <;> simp_all
  rw [hb, hbd]

theorem isKnownRoot_safe (t : zkcash_core.merkle_tree.MerkleTreeAccount) (root : Std.Array U8 32#usize)
    (hshape : TreeShape t) (hroot : Canonical root)
    (h : zkcash_core.merkle_tree.is_known_root t root = ok true) :
    LeanSpec.rootKnown (toTree t) (toF root) := by
  obtain ⟨b, hb, hiff⟩ := (WP.spec_equiv_exists _ _).mp (isKnownRootSpec t root hshape.2.1 hshape.2.2)
  have hbt : b = true := (Result.ok_injective (h.symm.trans hb)).symm
  obtain ⟨hne, j, hj⟩ := hiff.mp hbt
  simp only [LeanSpec.rootKnown, toTree, Set.mem_range]
  exact ⟨⟨j, congrArg toF hj⟩, fun h0 => hne (toF_injOn hroot zero_canonical (h0.trans toF_zero.symm))⟩

/-! ## `validate_fee` ↔ `feeSufficient` -/

private theorem u128MulSome (x y : U128) (h : x.val * y.val ≤ U128.max) :
    ∃ z : U128, x.checked_mul y = some z ∧ z.val = x.val * y.val := by
  have hspec := x.checked_mul_bv_spec y
  cases hc : x.checked_mul y with
  | none => rw [hc] at hspec; omega
  | some z => rw [hc] at hspec; exact ⟨z, rfl, hspec.2.1⟩

private theorem u128DivSome (x y : U128) (h : y.val ≠ 0) :
    ∃ z : U128, x.checked_div y = some z ∧ z.val = x.val / y.val := by
  have hspec := x.checked_div_bv_spec y
  cases hc : x.checked_div y with
  | none => rw [hc] at hspec; exact absurd hspec h
  | some z => rw [hc] at hspec; exact ⟨z, rfl, hspec.2.1⟩

private theorem u128SubSome (x y : U128) (h : y.val ≤ x.val) :
    ∃ z : U128, x.checked_sub y = some z ∧ z.val = x.val - y.val := by
  have hspec := x.checked_sub_bv_spec y
  cases hc : x.checked_sub y with
  | none => rw [hc] at hspec; omega
  | some z => rw [hc] at hspec; exact ⟨z, rfl, hspec.2.1⟩

/-- Everything `validate_fee` does after reading the amount `i` and the rate `i1`, shared
    verbatim by the deposit and the withdrawal branch. Under the bounds every `checked_*` step
    succeeds and both `u64` casts keep the value, so it is one comparison. -/
private theorem feeTailEq (i i1 : U128) (provided_fee : U64) (fee_error_margin : U16)
    (hi : i.val ≤ 2^63) (hi1 : i1.val ≤ 10000) (hm : fee_error_margin.val ≤ 10000) :
    (do
      let o ← lift (U128.checked_mul i i1)
      let r ← core.option.Option.ok_or o zkcash_core.error.ErrorCode.ArithmeticOverflow
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let o1 ← lift (U128.checked_div val 10000#u128)
        let r1 ← core.option.Option.ok_or o1 zkcash_core.error.ErrorCode.ArithmeticOverflow
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let expected_fee ← lift (UScalar.cast .U64 val1)
          if expected_fee > 0#u64
          then
            let i2 ← lift (UScalar.cast .U128 fee_error_margin)
            let o2 ← lift (U128.checked_sub 10000#u128 i2)
            let r2 ←
              core.option.Option.ok_or o2 zkcash_core.error.ErrorCode.ArithmeticOverflow
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              let i3 ← lift (UScalar.cast .U128 expected_fee)
              let o3 ← lift (U128.checked_mul i3 val2)
              let r3 ←
                core.option.Option.ok_or o3 zkcash_core.error.ErrorCode.ArithmeticOverflow
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue val3 =>
                let o4 ← lift (U128.checked_div val3 10000#u128)
                let r4 ←
                  core.option.Option.ok_or o4 zkcash_core.error.ErrorCode.ArithmeticOverflow
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let min_acceptable_fee ← lift (UScalar.cast .U64 val4)
                  if provided_fee >= min_acceptable_fee
                  then ok (core.result.Result.Ok ())
                  else
                    ok (core.result.Result.Err zkcash_core.error.ErrorCode.InvalidFeeAmount)
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit (core.convert.FromSame zkcash_core.error.ErrorCode) residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit (core.convert.FromSame zkcash_core.error.ErrorCode) residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit (core.convert.FromSame zkcash_core.error.ErrorCode) residual
          else
            if provided_fee >= 0#u64
            then ok (core.result.Result.Ok ())
            else ok (core.result.Result.Err zkcash_core.error.ErrorCode.InvalidFeeAmount)
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit (core.convert.FromSame zkcash_core.error.ErrorCode) residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame zkcash_core.error.ErrorCode) residual)
      = ok (if provided_fee.val ≥ i.val * i1.val / 10000 * (10000 - fee_error_margin.val) / 10000
        then core.result.Result.Ok () else core.result.Result.Err zkcash_core.error.ErrorCode.InvalidFeeAmount) := by
  simp only [lift, bind_tc_ok]
  obtain ⟨val, hval, hvalv⟩ := u128MulSome i i1 (by
    calc i.val * i1.val ≤ 2^63 * 10000 := Nat.mul_le_mul hi hi1
      _ ≤ U128.max := by scalar_tac)
  simp only [hval, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok]
  obtain ⟨val1, hval1, hval1v⟩ := u128DivSome val 10000#u128 (by simp)
  simp only [hval1, bind_tc_ok]
  have hval1e : val1.val = i.val * i1.val / 10000 := by rw [hval1v, hvalv]; rfl
  have hle : i.val * i1.val / 10000 ≤ i.val :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm 10000]; exact Nat.mul_le_mul_left _ hi1)
  have hval1b : val1.val < 2^64 := by omega
  have hef : (UScalar.cast .U64 val1).val = val1.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ hval1b
  rw [← hval1e]
  by_cases hz : UScalar.cast .U64 val1 > 0#u64
  · rw [if_pos hz]
    have hmr : (UScalar.cast .U128 fee_error_margin).val = fee_error_margin.val := by simp
    obtain ⟨val2, hval2, hval2v⟩ := u128SubSome 10000#u128 (UScalar.cast .U128 fee_error_margin)
      (by rw [hmr]; simp; omega)
    simp only [hval2, bind_tc_ok]
    have hval2e : val2.val = 10000 - fee_error_margin.val := by rw [hval2v, hmr]; rfl
    have hcc : (UScalar.cast .U128 (UScalar.cast .U64 val1)).val = val1.val := by
      simp only [UScalar.cast_val_eq, hef]; simp
    obtain ⟨val3, hval3, hval3v⟩ := u128MulSome (UScalar.cast .U128 (UScalar.cast .U64 val1))
      val2 (by
        rw [hcc, hval2e]
        calc val1.val * (10000 - fee_error_margin.val) ≤ 2^63 * 10000 :=
              Nat.mul_le_mul (by omega) (by omega)
          _ ≤ U128.max := by scalar_tac)
    simp only [hval3, bind_tc_ok]
    obtain ⟨val4, hval4, hval4v⟩ := u128DivSome val3 10000#u128 (by simp)
    simp only [hval4, bind_tc_ok]
    have hval4e : val4.val = val1.val * (10000 - fee_error_margin.val) / 10000 := by
      rw [hval4v, hval3v, hcc, hval2e]; rfl
    have hval4le : val4.val ≤ val1.val := by
      rw [hval4e]
      exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm 10000]; exact Nat.mul_le_mul_left _ (by omega))
    have hval4b : val4.val < 2^64 := by omega
    have hmin : (UScalar.cast .U64 val4).val = val4.val :=
      UScalar.cast_val_mod_pow_of_inBounds_eq _ _ hval4b
    have hiff : provided_fee ≥ UScalar.cast .U64 val4 ↔
        provided_fee.val ≥ val1.val * (10000 - fee_error_margin.val) / 10000 := by
      rw [← hval4e, ← hmin]; rfl
    by_cases hfee : provided_fee ≥ UScalar.cast .U64 val4
    · rw [if_pos hfee, if_pos (hiff.mp hfee)]
    · rw [if_neg hfee, if_neg (fun h => hfee (hiff.mpr h))]
  · have hz0 : (UScalar.cast .U64 val1).val = 0 := by
      have : ¬ (UScalar.cast .U64 val1).val > 0 := hz
      omega
    have hge : provided_fee ≥ 0#u64 := by
      show (0#u64).val ≤ provided_fee.val; simp
    rw [if_neg hz, if_pos hge, ← hef, hz0, if_pos (by simp)]

theorem validateFee_iff (extAmt : I64) (fee : U64) (c : zkcash_core.admin.GlobalConfig)
    (t : zkcash_core.merkle_tree.MerkleTreeAccount)
    (hd : c.deposit_fee_rate.val ≤ 10000) (hw : c.withdrawal_fee_rate.val ≤ 10000)
    (hm : c.fee_error_margin.val ≤ 10000) :
    zkcash_core.utils.validate_fee extAmt fee c.deposit_fee_rate c.withdrawal_fee_rate
        c.fee_error_margin = ok (.Ok ()) ↔
      extAmt.val ≠ -9223372036854775808 ∧ LeanSpec.feeSufficient (toConfig c t) extAmt.val fee.val := by
  simp only [LeanSpec.feeSufficient, toConfig]
  by_cases hpos : extAmt > 0#i64
  · have hpos' : extAmt.val > 0 := by scalar_tac
    have hext : (IScalar.hcast .U128 extAmt).val = extAmt.val.natAbs := by
      simp [IScalar.hcast_val_eq]; scalar_tac
    have hcode : zkcash_core.utils.validate_fee extAmt fee c.deposit_fee_rate c.withdrawal_fee_rate
        c.fee_error_margin = ok (if fee.val ≥ (IScalar.hcast .U128 extAmt).val *
          (UScalar.cast .U128 c.deposit_fee_rate).val / 10000 * (10000 - c.fee_error_margin.val) / 10000
          then core.result.Result.Ok () else core.result.Result.Err zkcash_core.error.ErrorCode.InvalidFeeAmount) := by
      unfold zkcash_core.utils.validate_fee
      rw [if_pos hpos]
      have ht := feeTailEq (IScalar.hcast .U128 extAmt) (UScalar.cast .U128 c.deposit_fee_rate) fee
        c.fee_error_margin (by rw [hext]; scalar_tac) (by simp; omega) hm
      simp only [lift, bind_tc_ok] at ht ⊢
      exact ht
    rw [hcode, if_pos hpos', hext]
    have hv : extAmt.val ≠ -9223372036854775808 := by omega
    have hr : (UScalar.cast .U128 c.deposit_fee_rate).val = c.deposit_fee_rate.val := by simp
    rw [hr]
    split_ifs with hc <;> simp [Result.ok.injEq, hv] <;> omega
  · have hpos' : ¬ extAmt.val > 0 := by scalar_tac
    by_cases hneg : extAmt < 0#i64
    · by_cases hmin : extAmt = core.num.I64.MIN
      · have hv : extAmt.val = -9223372036854775808 := by rw [hmin]; rfl
        have hnone : core.num.I64.checked_neg extAmt = ok none := by
          rw [hmin]; simp [core.num.I64.checked_neg, IScalar.neg, IScalar.tryMk, IScalar.tryMkOpt,
            Option.ofResult, IScalar.cMin, IScalar.cMax, I64.rMin, I64.rMax]
        have hcode : zkcash_core.utils.validate_fee extAmt fee c.deposit_fee_rate c.withdrawal_fee_rate
            c.fee_error_margin = ok (core.result.Result.Err zkcash_core.error.ErrorCode.ArithmeticOverflow) := by
          unfold zkcash_core.utils.validate_fee
          rw [if_neg hpos, if_pos hneg, hnone]
          simp [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
        rw [hcode]; simp [Result.ok.injEq, hv]
      · have hneg' : extAmt.val < 0 := by scalar_tac
        have hv : extAmt.val ≠ -9223372036854775808 := by
          intro h; apply hmin; rw [IScalar.eq_equiv, h]; rfl
        obtain ⟨y, hy, hyv⟩ : ∃ y, IScalar.neg extAmt = ok y ∧ y.val = -extAmt.val := by
          have := IScalar.neg_step extAmt (by intro h; apply hv; rw [h]; simp [I64.min_eq])
          cases hr : IScalar.neg extAmt <;> simp_all
        have hwd : (UScalar.cast .U128 (IScalar.hcast .U64 y)).val = extAmt.val.natAbs := by
          simp [IScalar.hcast_val_eq, hyv]; scalar_tac
        have hcode : zkcash_core.utils.validate_fee extAmt fee c.deposit_fee_rate c.withdrawal_fee_rate
            c.fee_error_margin = ok (if fee.val ≥ (UScalar.cast .U128 (IScalar.hcast .U64 y)).val *
              (UScalar.cast .U128 c.withdrawal_fee_rate).val / 10000 * (10000 - c.fee_error_margin.val) / 10000
              then core.result.Result.Ok () else core.result.Result.Err zkcash_core.error.ErrorCode.InvalidFeeAmount) := by
          unfold zkcash_core.utils.validate_fee
          rw [if_neg hpos, if_pos hneg]
          have ht := feeTailEq (UScalar.cast .U128 (IScalar.hcast .U64 y))
            (UScalar.cast .U128 c.withdrawal_fee_rate) fee c.fee_error_margin
            (by rw [hwd]; scalar_tac) (by simp; omega) hm
          simp only [core.num.I64.checked_neg, hy, Option.ofResult, Result.match.ok, lift, bind_tc_ok,
            core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch] at ht ⊢
          exact ht
        rw [hcode, if_neg hpos', hwd]
        have hr : (UScalar.cast .U128 c.withdrawal_fee_rate).val = c.withdrawal_fee_rate.val := by simp
        rw [hr]
        split_ifs with hc <;> simp [Result.ok.injEq, hv] <;> omega
    · have hz : extAmt.val = 0 := by scalar_tac
      have hcode : zkcash_core.utils.validate_fee extAmt fee c.deposit_fee_rate c.withdrawal_fee_rate
          c.fee_error_margin = ok (core.result.Result.Ok ()) := by
        unfold zkcash_core.utils.validate_fee
        rw [if_neg hpos, if_neg hneg]
      rw [hcode]; simp [hz]

/-- `validate_fee` checks `feeSufficient` and `amountsInRange`. -/
theorem validateFee_eq_spec (extAmt : I64) (fee : U64) (c : zkcash_core.admin.GlobalConfig)
    (t : zkcash_core.merkle_tree.MerkleTreeAccount)
    (hd : c.deposit_fee_rate.val ≤ 10000) (hw : c.withdrawal_fee_rate.val ≤ 10000)
    (hm : c.fee_error_margin.val ≤ 10000) :
    zkcash_core.utils.validate_fee extAmt fee c.deposit_fee_rate c.withdrawal_fee_rate
        c.fee_error_margin = ok (.Ok ()) ↔
      LeanSpec.feeSufficient (toConfig c t) extAmt.val fee.val ∧
        LeanSpec.amountsInRange extAmt.val fee.val := by
  rw [validateFee_iff extAmt fee c t hd hw hm]
  have hlo : -2 ^ 63 ≤ extAmt.val := by scalar_tac
  have hhi : extAmt.val < 2 ^ 63 := by scalar_tac
  have hfee : fee.val < 2 ^ 64 := by scalar_tac
  simp only [LeanSpec.amountsInRange]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by omega, hhi, hfee⟩
  · rintro ⟨h2, h1, -, -⟩; exact ⟨by omega, h2⟩

end Connection
