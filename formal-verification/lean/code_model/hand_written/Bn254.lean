-- SHARED trusted base: the BN254 scalar field.
--
-- Hand-owned, like the `*External.lean` files that import it. `extract.sh` never
-- generates or touches anything under Common/.
--
-- Why this file exists: `bn254_r` and `FrShim` were previously declared once per model
-- (TransactShim, VerifyProofShim, CheckPublicAmountShim). Those were `def`s with equal
-- bodies, so the duplication was safe but pointless. Declaring them ONCE here removes it.
-- (The models still cannot be imported into one Lean file: their GENERATED code overlaps,
-- which Common/ cannot fix. See MODEL_COVERAGE.md.)
import Aeneas
import Mathlib.Data.ZMod.Basic
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-- BN254 scalar-field modulus `r` -- the order of the BN254 prime-order group, i.e.
    `ark_bn254::Fr::MODULUS`. Identical to `p` in `Spec/privacy_cash_spec.lean`, which is
    the bridge a theorem relating this model to that spec would go through. -/
def bn254_r : ℕ :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- [zkcash::fr_shim::FrShim], modeled as the finite field 𝔽ᵣ = `ZMod bn254_r`.
    `abbrev` (not `def`) so that ZMod's `CommRing`/`DecidableEq` instances are found
    automatically when the model writes `a + b`, `a = b`, etc. on FrShim.
    Source: 'programs/zkcash/src/fr_shim.rs', lines 19:0-19:32 -/
abbrev fr_shim.FrShim : Type := ZMod bn254_r
