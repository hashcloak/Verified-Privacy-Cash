/-
Hand-written Lean definitions for Rust library functions that zkcash_core uses
but Aeneas's standard library does not provide yet. Aeneas lists them in the
generated FunsExternal_Template.lean; each one here must match the Rust
semantics exactly (and is part of the trusted base until proven).
-/
import Aeneas
import PrivacyCash.Extracted.Types
open Aeneas Aeneas.Std Result

/-- [core::num::{i64}::checked_neg]: `None` exactly when `-x` overflows,
    i.e. when `x = i64::MIN`. Same shape as Aeneas's `checked_sub`. -/
@[rust_fun "core::num::{i64}::checked_neg"]
def core.num.I64.checked_neg (x : Std.I64) : Result (Option Std.I64) :=
  ok (Option.ofResult (IScalar.neg x))
