/-
The one Rust library function the extracted code needs that Aeneas does not
provide, `i64::checked_neg`, is defined by hand in
PrivacyCash/Extracted/FunsExternal.lean. This proves the definition has the
semantics the Rust documentation gives it, so it is no longer trusted:
`checked_neg` returns `None` exactly when `-x` overflows, i.e. when
`x = i64::MIN`, and otherwise `Some(-x)`.
-/
import PrivacyCash.Extracted.Funs
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Proofs

theorem option_ofResult_ofOption {α : Type} (o : Option α) (e : Error) :
    Option.ofResult (Result.ofOption o e) = o := by
  cases o <;> rfl

/-- `i64::checked_neg`: `None` iff `x = i64::MIN`, else `Some(-x)`. -/
theorem checked_neg_spec (x : Std.I64) :
    ∃ r, core.num.I64.checked_neg x = ok r ∧
      match r with
      | none => x.val = -2 ^ 63
      | some y => y.val = -x.val := by
  refine ⟨_, rfl, ?_⟩
  simp only [IScalar.neg, IScalar.tryMk, option_ofResult_ofOption]
  have h := IScalar.tryMkOpt_eq .I64 (-x.val)
  have hb := x.hBounds
  split
  · rename_i heq
    rw [heq] at h
    simp only [IScalar.inBounds, IScalarTy.numBits] at h hb
    omega
  · rename_i y heq
    rw [heq] at h
    exact h.1

end PrivacyCash.Proofs
