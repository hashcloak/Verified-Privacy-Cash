-- Specifications & proofs about the CheckPublicAmountShim model.
-- Lives OUTSIDE the aeneas-regenerated subdirs (CheckPublicAmountShim/, TransactShim/)
-- so `extract.sh` never touches it. Imports the generated model read-only.
import CheckPublicAmountShim.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
open zkcash

namespace CheckPublicAmountSpec

/-- Workflow sanity check (our first theorem about the extracted model):
    `i64::MIN` is always rejected by the first guard. -/
theorem min_rejected (fee : Std.U64) (bytes : Array Std.U8 32#usize) :
    utils.fv_check_public_amount_entry core.num.I64.MIN fee bytes = ok false := by
  simp [utils.fv_check_public_amount_entry]

/-- Deposit correctness: if `check_public_amount` accepts a deposit (`ext_amount ≥ 0`),
    then the supplied `public_amount` bytes decode to exactly `ext_amount - fee` in 𝔽ᵣ. -/
theorem deposit_spec
    (ext_amount : Std.I64) (fee : Std.U64) (bytes : Array Std.U8 32#usize)
    (hpos : (0 : Int) ≤ ext_amount.val)
    (hok : utils.fv_check_public_amount_entry ext_amount fee bytes = ok true) :
    fr_shim.FrShim.from_be_bytes_mod_order bytes
      = ok ((ext_amount.val : ZMod bn254_r) - (fee.val : ZMod bn254_r)) := by
  unfold utils.fv_check_public_amount_entry at hok
  have hge : ext_amount ≥ 0#i64 := by scalar_tac
  simp only [hge, ↓reduceIte, bind_tc_ok, lift,
             fr_shim.FrShim.from_u64,
             fr_shim.FrShim.Insts.CoreOpsArithSubFrShimFrShim.sub,
             fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq,
             core.cmp.PartialOrd.le.default, core.cmp.PartialOrd.le_body,
             fr_shim.FrShim.Insts.CoreCmpPartialOrdFrShim.partial_cmp,
             fr_shim.FrShim.from_be_bytes_mod_order] at hok ⊢
  split at hok
  · simp at hok
  · split at hok
    · simp at hok
    · simp only [Result.ok.injEq, decide_eq_true_eq] at hok
      have hbridge : (↑↑(IScalar.hcast UScalarTy.U64 ext_amount) : ZMod bn254_r)
          = (↑↑ext_amount : ZMod bn254_r) := by
        have hlt : ext_amount.val < 2 ^ 64 := by scalar_tac
        simp only [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq]
        rw [Int.emod_eq_of_lt hpos hlt, ← Int.cast_natCast (ext_amount.val.toNat),
            Int.toNat_of_nonneg hpos]
      rw [← hok, hbridge]

/-- Withdrawal correctness: if `check_public_amount` accepts a withdrawal
    (`ext_amount < 0`), the `public_amount` bytes still decode to `ext_amount - fee`
    in 𝔽ᵣ (here `ext_amount` is a *negative* field element, so this is `-(|ext|+fee)`). -/
theorem withdrawal_spec
    (ext_amount : Std.I64) (fee : Std.U64) (bytes : Array Std.U8 32#usize)
    (hneg : ext_amount.val < 0)
    (hok : utils.fv_check_public_amount_entry ext_amount fee bytes = ok true) :
    fr_shim.FrShim.from_be_bytes_mod_order bytes
      = ok ((ext_amount.val : ZMod bn254_r) - (fee.val : ZMod bn254_r)) := by
  unfold utils.fv_check_public_amount_entry at hok
  have hnge : ¬ (ext_amount ≥ 0#i64) := by scalar_tac
  simp only [hnge, ↓reduceIte, bind_tc_ok, lift,
             fr_shim.FrShim.from_u64,
             fr_shim.FrShim.Insts.CoreOpsArithAddFrShimFrShim.add,
             fr_shim.FrShim.Insts.CoreOpsArithNegFrShim.neg,
             fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq,
             core.num.I64.checked_neg,
             fr_shim.FrShim.from_be_bytes_mod_order] at hok
  split at hok
  · simp at hok
  · cases hne_eq : IScalar.neg ext_amount with
    | fail e => simp [hne_eq] at hok
    | div => simp [hne_eq] at hok
    | ok vneg =>
      simp only [hne_eq, bind_tc_ok, Result.ok.injEq, decide_eq_true_eq] at hok
      have hvneg : vneg.val = -ext_amount.val := by
        have h := IScalar.tryMk_eq IScalarTy.I64 (-ext_amount.val)
        unfold IScalar.neg at hne_eq
        rw [hne_eq] at h
        exact h.1
      have hvpos : (0 : Int) ≤ vneg.val := by rw [hvneg]; omega
      have hbridge : (↑↑(IScalar.hcast UScalarTy.U64 vneg) : ZMod bn254_r)
          = -(ext_amount.val : ZMod bn254_r) := by
        have hvlt : vneg.val < 2 ^ 64 := by rw [hvneg]; scalar_tac
        simp only [IScalar.hcast_val_eq, UScalarTy.U64_numBits_eq]
        rw [Int.emod_eq_of_lt hvpos hvlt, ← Int.cast_natCast vneg.val.toNat,
            Int.toNat_of_nonneg hvpos, hvneg]
        push_cast; ring
      simp only [fr_shim.FrShim.from_be_bytes_mod_order]
      rw [← hok, hbridge]
      congr 1
      ring

end CheckPublicAmountSpec
