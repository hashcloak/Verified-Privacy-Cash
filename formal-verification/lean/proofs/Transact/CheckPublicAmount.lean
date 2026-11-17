import code_model.generated.Funs
import code_model.hand_written.SyscallContracts
open Aeneas Aeneas.Std Result ControlFlow
namespace zkcash

theorem I64_MIN_val : core.num.I64.MIN.val = -2 ^ 63 := by
  simp [core.num.I64.MIN, I64.rMin]

theorem two_pow_64_lt_r : 2 ^ 64 < bn254_r := by unfold bn254_r; norm_num

/-- `check_public_amount` (its model twin `fv_check_public_amount_entry`) accepts exactly when
    1. `ext_amount` is not `i64::MIN`,
    2. a deposit (`ext_amount ≥ 0`) is larger than its fee, and
    3. the proof's public amount, read big-endian and reduced mod r, is `ext_amount − fee` mod r.
    It never fails: the result is always `ok true` or `ok false`. -/
theorem fv_check_public_amount_entry_spec (ext_amount : Std.I64) (fee : Std.U64)
    (public_amount_bytes : Array Std.U8 32#usize) :
    utils.fv_check_public_amount_entry ext_amount fee public_amount_bytes ⦃ b =>
      b = true ↔
        ext_amount.val ≠ -2 ^ 63 ∧
        (0 ≤ ext_amount.val → (fee.val : ℤ) < ext_amount.val) ∧
        ((ext_amount.val - fee.val : ℤ) : ZMod bn254_r) =
          ((curve_shim.natOfBE public_amount_bytes : ℕ) : ZMod bn254_r) ⦄ := by
  by_cases hmin : ext_amount = core.num.I64.MIN
  · unfold utils.fv_check_public_amount_entry
    simp only [hmin, if_true, WP.spec_ok, Bool.false_eq_true, false_iff, not_and, I64_MIN_val]
    intro h; exact absurd rfl h
  unfold utils.fv_check_public_amount_entry
  have hne : ext_amount.val ≠ -2 ^ 63 := by
    intro h; apply hmin; apply IScalar.eq_of_val_eq; rw [h, I64_MIN_val]
  simp only [hmin, if_false]
  by_cases hpos : ext_amount >= 0#i64
  · simp only [hpos, if_true, fr_shim.FrShim.from_u64, bind_tc_ok, lift, core.cmp.PartialOrd.le.default,
      core.cmp.PartialOrd.le_body, fr_shim.FrShim.Insts.CoreCmpPartialOrdFrShim.partial_cmp,
      fr_shim.FrShim.Insts.CoreOpsArithSubFrShimFrShim.sub, fr_shim.FrShim.from_be_bytes_mod_order,
      fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq]
    have h0 : 0 ≤ ext_amount.val := by scalar_tac
    have hc : ((IScalar.hcast UScalarTy.U64 ext_amount).val : ℕ) = ext_amount.val.toNat := by
      rw [IScalar.hcast_val_eq]; congr 1; have := ext_amount.hmax; simp at this ⊢; omega
    have hv1 : ((ext_amount.val.toNat : ℕ) : ZMod bn254_r).val = ext_amount.val.toNat :=
      ZMod.val_cast_of_lt (by have := two_pow_64_lt_r; have := ext_amount.hmax; simp at this; omega)
    have hv2 : ((fee.val : ℕ) : ZMod bn254_r).val = fee.val :=
      ZMod.val_cast_of_lt (by have := two_pow_64_lt_r; scalar_tac)
    simp only [hc, hv1, hv2]
    have hcast : (((ext_amount.val.toNat : ℕ) : ZMod bn254_r)) = ((ext_amount.val : ℤ) : ZMod bn254_r) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h0]
    by_cases hle : ext_amount.val.toNat ≤ fee.val
    · have hcmp : (some (compare ext_amount.val.toNat fee.val) = some Ordering.lt ∨
          some (compare ext_amount.val.toNat fee.val) = some Ordering.eq) := by
        rcases Nat.lt_or_eq_of_le hle with h | h
        · left; simp [Nat.compare_eq_lt.mpr h]
        · right; simp [h]
      rw [if_pos (by simpa using hcmp), WP.spec_ok]
      simp only [Bool.false_eq_true, false_iff, not_and]
      intro _ hlt; have := hlt h0; omega
    · have hcmp : ¬ (some (compare ext_amount.val.toNat fee.val) = some Ordering.lt ∨
          some (compare ext_amount.val.toNat fee.val) = some Ordering.eq) := by
        simp only [Option.some.injEq, not_or]
        exact ⟨fun h => hle (Nat.le_of_lt (Nat.compare_eq_lt.mp h)), fun h => hle (le_of_eq (Nat.compare_eq_eq.mp h))⟩
      rw [if_neg (by simpa using hcmp), WP.spec_ok, decide_eq_true_iff, hcast]
      simp only [curve_shim.natOfBE]
      push_cast
      constructor
      · intro h; exact ⟨hne, fun _ => by omega, h⟩
      · rintro ⟨-, -, h⟩; exact h
  · have hneg : ext_amount.val < 0 := by scalar_tac
    have hmin' : ext_amount ≠ IScalar.min IScalarTy.I64 := by
      intro h; apply hne; rw [h]; simp [I64.min, I64.numBits]
    obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (IScalar.neg_step ext_amount hmin')
    simp only [hpos, if_false, core.num.I64.checked_neg, hmin, hy, bind_tc_ok, lift,
      fr_shim.FrShim.from_u64, fr_shim.FrShim.Insts.CoreOpsArithAddFrShimFrShim.add,
      fr_shim.FrShim.Insts.CoreOpsArithNegFrShim.neg, fr_shim.FrShim.from_be_bytes_mod_order,
      fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq, WP.spec_ok, decide_eq_true_iff]
    have hc : ((IScalar.hcast UScalarTy.U64 y).val : ℕ) = (-ext_amount.val).toNat := by
      rw [IScalar.hcast_val_eq, hyv]; congr 1; have := ext_amount.hmin; simp at this ⊢; omega
    have hcast : (((-ext_amount.val).toNat : ℕ) : ZMod bn254_r) = ((-ext_amount.val : ℤ) : ZMod bn254_r) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
    rw [hc, hcast]
    simp only [curve_shim.natOfBE]
    push_cast
    constructor
    · intro h; refine ⟨hne, fun h' => absurd h' (by omega), ?_⟩; rw [← h]; ring
    · rintro ⟨-, -, h⟩; rw [← h]; ring
