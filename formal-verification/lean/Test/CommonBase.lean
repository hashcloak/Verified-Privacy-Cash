-- Regression guard for the Common/ refactor.
--
-- WHAT COMMON/ FIXED
-- `bn254_r`, `fr_shim.FrShim` and `curve_shim.G1Shim` used to be declared once per model.
-- The two `axiom curve_shim.G1Shim : Type` declarations were DIFFERENT TYPES even though
-- the text matched, so nothing proved in VerifyProofShim applied in TransactShim. There is
-- now one declaration of each, in Common/.
--
-- WHAT IS STILL BROKEN (and Common/ cannot fix)
-- The three models still cannot be imported together, for a different reason: their
-- GENERATED code overlaps. `fv_transact_entry` calls `fv_verify_proof_full_entry` and
-- `fv_check_public_amount_entry`, so TransactShim's closure already contains both smaller
-- models, and aeneas emits those functions again into each. Importing two models fails with
--     environment already contains 'zkcash.utils.fv_verify_proof_full_entry_loop0_loop3...'
-- Common/ is hand-owned and cannot deduplicate what aeneas regenerates. The fix is
-- single-root extraction -- one `charon rustc` run with every entry point, one Lean library.
-- See MODEL_COVERAGE.md section 0.
--
-- Consequence worth stating plainly: VerifyProofShim and CheckPublicAmountShim are strict
-- SUBSETS of TransactShim. They are development scaffolding, not components of the model.
import Common.FrShim
import Common.Curve
import TransactShim.Funs
open Aeneas Aeneas.Std Result

-- The scalar field is Mathlib's `ZMod r`, shared, not a per-model copy.
example : fr_shim.FrShim = ZMod bn254_r := rfl

-- The curve ops resolve to Common's single G1Shim declaration; TransactShim did not
-- shadow it with a copy of its own. If it did, this ascription would not typecheck.
noncomputable example : Array Std.U8 64#usize → Result (Option curve_shim.G1Shim) :=
  curve_shim.G1Shim.deserialize_uncompressed

-- The two endianness decodes really are different functions. `transact` compares
-- `from_le_bytes_mod_order` of the recomputed ext-data hash against `from_be_bytes_mod_order`
-- of the hash carried in the proof; if these ever collapsed, that check would be vacuous.
example : fr_shim.FrShim.from_le_bytes_mod_order ≠ fr_shim.FrShim.from_be_bytes_mod_order := by
  intro h
  have := congrFun h ⟨List.replicate 31 0#u8 ++ [1#u8], by simp⟩
  simp [fr_shim.FrShim.from_le_bytes_mod_order, fr_shim.FrShim.from_be_bytes_mod_order] at this
  exact absurd this (by first | omega | decide | norm_num)
