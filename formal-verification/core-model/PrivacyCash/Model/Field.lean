/-
The BN254 scalar field: the program's `ArkFr` (`programs/zkcash/src/utils.rs`),
which implements the extracted `zkcash_core::field::PrimeField` trait with
arkworks' `ark_bn254::Fr`.

arkworks is code compiled into the program, so the model DEFINES it rather
than leaving it a parameter: the field is the integers mod r (`ZMod r`) and
each trait method is the operation its doc comment in `zkcash_core::field`
names. That this is what arkworks computes is checked on concrete inputs by
`Tests/FieldVectors.lean` (values at and around r and 2^256, random bytes, and
every operation on pairs of them), against the program's real `ArkFr`.
-/
import PrivacyCash.Model.Basic
import Mathlib.Data.ZMod.Basic
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Model

/-- The BN254 scalar field modulus r (`ark_bn254::Fr::MODULUS`). -/
def bn254ScalarModulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- BN254 scalar field elements, `ark_bn254::Fr`. -/
abbrev Fr := ZMod bn254ScalarModulus

/-- A 32-byte array read as a big-endian number. -/
def beNat (b : Std.Array U8 32#usize) : Nat := b.val.foldl (fun acc x => acc * 256 + x.val) 0

/-- A 32-byte array read as a little-endian number. -/
def leNat (b : Std.Array U8 32#usize) : Nat := b.val.foldr (fun x acc => acc * 256 + x.val) 0

/-- The program's `ArkFr`. arkworks orders field elements by their canonical
    value in `0..r`, which is what `le` compares. -/
def arkFr : zkcash_core.field.PrimeField Fr where
  coremarkerCopyInst := ⟨⟨fun a => ok a, fun _ b => ok b⟩⟩
  from_u64 x := ok (x.val : Fr)
  from_be_bytes_mod_order b := ok (beNat b : Fr)
  from_le_bytes_mod_order b := ok (leNat b : Fr)
  add a b := ok (a + b)
  sub a b := ok (a - b)
  neg a := ok (-a)
  le a b := ok (decide (a.val ≤ b.val))
  eq a b := ok (decide (a = b))

end PrivacyCash.Model
