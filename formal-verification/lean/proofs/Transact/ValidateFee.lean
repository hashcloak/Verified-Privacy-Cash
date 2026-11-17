import code_model.generated.Funs
open Aeneas Aeneas.Std Result ControlFlow
namespace zkcash

theorem bind_eq_ok' {α β : Type} (m : Result α) (f : α → Result β) (v : β) :
    (do let x ← m; f x) = ok v ↔ ∃ x, m = ok x ∧ f x = ok v := by
  cases m <;> simp

/-- `?` on an `Err` never produces `Ok`, whatever the error conversion does. -/
theorem from_residual_ne_ok {T E F : Type} (inst : core.convert.From F E) (r) (t : T) :
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual T inst r ≠
      ok (.Ok t) := by
  rcases r with x | e
  · exact x.casesOn
  · simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]
    intro h; obtain ⟨_, _, h⟩ := (bind_eq_ok' _ _ _).mp h; simp at h

/-- The fee rule `validate_fee` applies to an `amount` at `rate` basis points, with the error
    margin `margin`: the expected fee is `amount · rate / 10000`, truncated to 64 bits as the
    Rust `as u64` does; if it is 0 any fee is accepted, otherwise the margin must be at most
    10000 (else `10000 - margin` underflows and the call fails) and the fee must be at least
    `expected · (10000 − margin) / 10000`. -/
def feeAccepted (amount rate margin fee : ℕ) : Prop :=
  amount * rate / 10000 % 2 ^ 64 = 0 ∨
    (margin ≤ 10000 ∧ amount * rate / 10000 % 2 ^ 64 * (10000 - margin) / 10000 ≤ fee)

set_option hygiene false in
/-- The part of `validate_fee` shared by deposits and withdrawals, once the amount has been
    widened to `amt : U128` with `hamt : amt.val = n` and `hn : n < 2 ^ 64`: multiply by `rate`,
    divide, truncate, apply the margin, compare with the fee. Proves the goal
    `<that code> = ok (.Ok ()) ↔ feeAccepted n rate.val fee_error_margin.val provided_fee.val`. -/
local macro "fee_tail" : tactic => `(tactic| (
  have hmaxR := rate.hmax; have hmaxM := fee_error_margin.hmax; have hmaxF := provided_fee.hmax
  have hB : (UScalar.cast UScalarTy.U128 rate).val = rate.val := by
    rw [UScalar.cast_val_eq]; simp at *; omega
  -- amount * rate
  have hp := U128.checked_mul_bv_spec amt (UScalar.cast UScalarTy.U128 rate)
  rcases h1 : U128.checked_mul amt (UScalar.cast UScalarTy.U128 rate) with _ | p
  · rw [h1, hamt, hB, U128.max_eq] at hp
    have hr : rate.val < 2 ^ 16 := by simpa using hmaxR
    have := Nat.mul_lt_mul'' hn hr; omega
  rw [h1, hamt, hB] at hp; obtain ⟨-, hpv, -⟩ := hp
  simp only [core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  -- / 10000
  have hq := U128.checked_div_bv_spec p 10000#u128
  rcases h2 : p.checked_div 10000#u128 with _ | q
  · rw [h2] at hq; simp at hq
  rw [h2] at hq; obtain ⟨-, hqv, -⟩ := hq
  simp only [bind_tc_ok]
  have he : (UScalar.cast UScalarTy.U64 q).val = n * rate.val / 10000 % 2 ^ 64 := by
    rw [UScalar.cast_val_eq, hqv, hpv]; simp
  have hmarg : (UScalar.cast UScalarTy.U128 fee_error_margin).val = fee_error_margin.val := by
    rw [UScalar.cast_val_eq]; simp at *; omega
  have heLt : (UScalar.cast UScalarTy.U64 q).val < 2 ^ 64 := by rw [he]; exact Nat.mod_lt _ (by norm_num)
  by_cases hpos_e : UScalar.cast UScalarTy.U64 q > 0#u64
  swap
  · -- expected fee is 0: any fee is accepted
    have he0 : n * rate.val / 10000 % 2 ^ 64 = 0 := by rw [← he]; scalar_tac
    simp only [hpos_e, if_false, feeAccepted, he0, true_or, iff_true]
    have : provided_fee ≥ 0#u64 := by scalar_tac
    simp [this]
  simp only [hpos_e, if_true]
  have hep : 0 < n * rate.val / 10000 % 2 ^ 64 := by rw [← he]; scalar_tac
  have hs := U128.checked_sub_bv_spec 10000#u128 (UScalar.cast UScalarTy.U128 fee_error_margin)
  rcases h3 : U128.checked_sub 10000#u128 (UScalar.cast UScalarTy.U128 fee_error_margin) with _ | s
  · -- margin > 10000: the subtraction underflows and the call returns an error
    rw [h3, hmarg] at hs; simp at hs
    simp only [bind_tc_ok]
    have hne := from_residual_ne_ok anchor_lang.error.Error.Insts.CoreConvertFromErrorCode
      (core.result.Result.Err ErrorCode.ArithmeticOverflow) ()
    simp only [hne, false_iff, feeAccepted, not_or, not_and, not_le]
    exact ⟨by omega, fun h => absurd h (by omega)⟩
  rw [h3, hmarg] at hs; obtain ⟨hsle, hsv, -⟩ := hs
  simp only [bind_tc_ok]
  have hc64 : (UScalar.cast UScalarTy.U128 (UScalar.cast UScalarTy.U64 q)).val = (UScalar.cast UScalarTy.U64 q).val := by
    rw [UScalar.cast_val_eq]; simp; omega
  have hm := U128.checked_mul_bv_spec (UScalar.cast UScalarTy.U128 (UScalar.cast UScalarTy.U64 q)) s
  rcases h4 : U128.checked_mul (UScalar.cast UScalarTy.U128 (UScalar.cast UScalarTy.U64 q)) s with _ | m
  · rw [h4, hc64, U128.max_eq] at hm
    have : s.val ≤ 10000 := by rw [hsv]; simp
    have := Nat.mul_le_mul (Nat.le_of_lt heLt) this; omega
  rw [h4, hc64] at hm; obtain ⟨-, hmv, -⟩ := hm
  simp only [bind_tc_ok]
  have hk := U128.checked_div_bv_spec m 10000#u128
  rcases h5 : m.checked_div 10000#u128 with _ | k
  · rw [h5] at hk; simp at hk
  rw [h5] at hk; obtain ⟨-, hkv, -⟩ := hk
  simp only [bind_tc_ok]
  have hkval : (UScalar.cast UScalarTy.U64 k).val =
      n * rate.val / 10000 % 2 ^ 64 * (10000 - fee_error_margin.val) / 10000 := by
    have hs' : s.val = 10000 - fee_error_margin.val := by rw [hsv]; simp
    have hkv' : k.val = (UScalar.cast UScalarTy.U64 q).val * (10000 - fee_error_margin.val) / 10000 := by
      rw [hkv, hmv, hs']; simp
    rw [UScalar.cast_val_eq, hkv', he]
    apply Nat.mod_eq_of_lt
    calc _ ≤ n * rate.val / 10000 % 2 ^ 64 * 10000 / 10000 := by
            apply Nat.div_le_div_right; apply Nat.mul_le_mul_left; omega
         _ < 2 ^ 64 := by simp; exact Nat.mod_lt _ (by norm_num)
  have hmarg_le : fee_error_margin.val ≤ 10000 := by simpa using hsle
  by_cases hfee : provided_fee ≥ UScalar.cast UScalarTy.U64 k
  · simp only [hfee, if_true, true_iff, feeAccepted]
    right; exact ⟨hmarg_le, by rw [← hkval]; scalar_tac⟩
  · simp only [hfee, if_false]
    constructor
    · intro h; obtain ⟨_, _, h⟩ := (bind_eq_ok' _ _ _).mp h
      obtain ⟨_, _, h⟩ := (bind_eq_ok' _ _ _).mp h
      obtain ⟨_, _, h⟩ := (bind_eq_ok' _ _ _).mp h
      obtain ⟨_, _, h⟩ := (bind_eq_ok' _ _ _).mp h
      simp at h
    · rintro (h | ⟨-, h⟩)
      · omega
      · exfalso; apply hfee; rw [← hkval] at h; scalar_tac))

/-- `validate_fee` returns `Ok(())` exactly when
    - a deposit (`ext_amount > 0`) pays at least the deposit fee rule on `ext_amount`, and
    - a withdrawal (`ext_amount < 0`) is not `i64::MIN` and pays at least the withdrawal fee
      rule on `|ext_amount|`;
    `ext_amount = 0` always passes. See `feeAccepted` for the rule, including the `as u64`
    truncation and the margin check. -/
theorem validate_fee_ok_iff (ext_amount : Std.I64) (provided_fee : Std.U64)
    (deposit_fee_rate withdrawal_fee_rate fee_error_margin : Std.U16) :
    utils.validate_fee ext_amount provided_fee deposit_fee_rate withdrawal_fee_rate fee_error_margin = ok (.Ok ()) ↔
      (0 < ext_amount.val →
        feeAccepted ext_amount.val.toNat deposit_fee_rate.val fee_error_margin.val provided_fee.val) ∧
      (ext_amount.val < 0 → ext_amount.val ≠ -2 ^ 63 ∧
        feeAccepted (-ext_amount.val).toNat withdrawal_fee_rate.val fee_error_margin.val provided_fee.val) := by
  unfold utils.validate_fee
  have hmaxE := ext_amount.hmax; have hminE := ext_amount.hmin
  by_cases hpos : ext_amount > 0#i64
  · have hpos' : 0 < ext_amount.val := by scalar_tac
    simp only [hpos, if_true, lift, bind_tc_ok, hpos', true_implies, show ¬ ext_amount.val < 0 by omega,
      false_implies, and_true]
    generalize hamtdef : IScalar.hcast UScalarTy.U128 ext_amount = amt
    have hamt : amt.val = ext_amount.val.toNat := by
      rw [← hamtdef, IScalar.hcast_val_eq]; congr 1; simp at *; omega
    have hn : ext_amount.val.toNat < 2 ^ 64 := by simp at hmaxE; omega
    generalize ext_amount.val.toNat = n at hamt hn ⊢
    generalize deposit_fee_rate = rate
    fee_tail
  by_cases hneg : ext_amount < 0#i64
  swap
  · have h0 : ext_amount.val = 0 := by scalar_tac
    simp only [hpos, hneg, if_false, h0, lt_irrefl, false_implies, and_self]
  have hneg' : ext_amount.val < 0 := by scalar_tac
  simp only [hpos, hneg, if_false, if_true, hneg', true_implies, show ¬ 0 < ext_amount.val by omega,
    false_implies, true_and]
  by_cases hmin : ext_amount = core.num.I64.MIN
  · have hminv : ext_amount.val = -2 ^ 63 := by rw [hmin]; simp [core.num.I64.MIN, I64.rMin]
    simp only [core.num.I64.checked_neg, hmin, if_true, bind_tc_ok, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch]
    have hne := from_residual_ne_ok anchor_lang.error.Error.Insts.CoreConvertFromErrorCode
      (core.result.Result.Err ErrorCode.ArithmeticOverflow) ()
    simp only [hne, false_iff, not_and]
    intro h; exact absurd (by rw [← hmin]; exact hminv) h
  have hne : ext_amount.val ≠ -2 ^ 63 := by
    intro h; apply hmin; apply IScalar.eq_of_val_eq; rw [h]; simp [core.num.I64.MIN, I64.rMin]
  have hmin' : ext_amount ≠ IScalar.min IScalarTy.I64 := by
    intro h; apply hne; rw [h]; simp [I64.min, I64.numBits]
  obtain ⟨y, hy, hyv⟩ := WP.spec_imp_exists (IScalar.neg_step ext_amount hmin')
  simp only [core.num.I64.checked_neg, hmin, if_false, hy, bind_tc_ok, core.option.Option.ok_or,
    core.result.Result.Insts.CoreOpsTry.branch, lift, ne_eq, hne, not_false_eq_true, true_and]
  generalize hamtdef : UScalar.cast UScalarTy.U128 (IScalar.hcast UScalarTy.U64 y) = amt
  have hamt : amt.val = (-ext_amount.val).toNat := by
    rw [← hamtdef, UScalar.cast_val_eq, IScalar.hcast_val_eq, hyv]; simp at *; omega
  have hn : (-ext_amount.val).toNat < 2 ^ 64 := by simp at hminE; omega
  generalize (-ext_amount.val).toNat = n at hamt hn ⊢
  generalize withdrawal_fee_rate = rate
  fee_tail
