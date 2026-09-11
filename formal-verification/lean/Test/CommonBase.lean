-- Regression guard for the shared trusted base in Common/.
--
-- WHY THIS EXISTS
-- `bn254_r`, `fr_shim.FrShim` and `curve_shim.G1Shim` used to be declared once per model.
-- The two `axiom curve_shim.G1Shim : Type` declarations were DIFFERENT TYPES even though the
-- text matched, so nothing proved about one applied to the other. There is now exactly one
-- declaration of each, in Common/, and this file stops building if a copy ever comes back.
--
-- The other half of that duplication was in the GENERATED code, and Common/ could not fix it:
-- three charon runs emitted fv_verify_proof_full_entry and fv_check_public_amount_entry into
-- more than one library, so importing two models failed with
--     environment already contains 'zkcash.utils.fv_verify_proof_full_entry_loop0_loop3...'
-- Common/ is hand-owned and cannot deduplicate what aeneas regenerates. That half was fixed by
-- extracting every entry point in ONE charon/aeneas run (extract.sh) -- which is
-- what lean/Zkcash is, and why the three per-entry-point libraries are gone.
import Common.FrShim
import Common.Curve
import Zkcash.Funs
open Aeneas Aeneas.Std Result

-- The scalar field is Mathlib's `ZMod r`, shared, not a per-model copy.
example : fr_shim.FrShim = ZMod bn254_r := rfl

-- The curve ops resolve to Common's single G1Shim declaration; the model did not shadow it
-- with one of its own. If it had, this ascription would not typecheck.
noncomputable example : Array Std.U8 64#usize → Result (Option curve_shim.G1Shim) :=
  curve_shim.G1Shim.deserialize_uncompressed

-- The two endianness decodes really are different functions. `transact` compares
-- `from_le_bytes_mod_order` of the recomputed ext-data hash against `from_be_bytes_mod_order`
-- of the hash carried in the proof; if these ever collapsed, that check would be vacuous.
example : fr_shim.FrShim.from_le_bytes_mod_order ≠ fr_shim.FrShim.from_be_bytes_mod_order := by
  intro h
  have := congrFun h ⟨List.replicate 31 0#u8 ++ [1#u8], by simp⟩
  simp [fr_shim.FrShim.from_le_bytes_mod_order, fr_shim.FrShim.from_be_bytes_mod_order] at this
  exact absurd this (by decide)
