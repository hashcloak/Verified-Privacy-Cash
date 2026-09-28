-- Trusted base (hand-written): what the three alt_bn128 syscalls PROMISE.
--
-- The syscalls run inside the Solana validator, so Lean never gets their bodies. Curve.lean only
-- declares their types: enough to write code that calls them, not enough to reason about what they
-- return. This file adds that missing half -- what a SUCCESSFUL answer means.
--
-- INDEPENDENT OF THE SPECIFICATION. Nothing here imports Spec/. The curve groups and the pairing
-- are the model's own: parameters of the class, carrying only the structure the syscalls' promises
-- need. Borrowing the specification's definitions would make any later theorem connecting model
-- and specification partly the specification agreeing with itself. Connecting the two is a
-- separate, later "bridge" step.
--
-- DELIBERATELY NOT ASSUMED, because the syscalls' behaviour does not require it:
--   * that the pairing is bilinear -- the code only checks that four pairings multiply to 1;
--   * that the groups have order r, or that scalars live in the field modulo r -- the
--     multiplication syscall uses the plain 256-bit integer, so the promise does too.
-- Those are facts about the Groth16 mathematics. They belong to the bridge, not to the model.
--
-- A CLASS, NOT AXIOMS. A theorem relying on these promises carries `[AltBn128Syscalls ..]` in its
-- signature. None of them can let Lean derive `False` -- at worst a theorem applies to nothing --
-- and they add nothing to `#print axioms`.
--
-- ONLY THE SOUNDNESS DIRECTION: "if the syscall returned a result, this is what it computed".
-- Nothing is said about failures, or about valid inputs being accepted (completeness).
--
-- JUSTIFICATION, read from source rather than assumed: solana-bn254 2.2.2, native implementation,
-- formal-verification/vendor/solana-bn254/src/lib.rs, which depends on arkworks 0.4.x.
--   * Points are decoded by `TryFrom<PodG1>` / `TryFrom<PodG2>`: big-endian bytes; all zeros is the
--     point at infinity; otherwise arkworks `deserialize_with_mode(.., Validate::Yes)` -- range
--     checks, on-curve, and for G2 a real subgroup check (G2's cofactor is not 1). One decoder
--     serves all three syscalls, which is why a single `decodeG1` / `decodeG2` is used below.
--   * Addition returns P + Q. Multiplication returns k·P for the 32-byte big-endian integer k,
--     unreduced. The pairing returns the 32-byte big-endian integer 1 when the product of the
--     pairings is the identity, and 0 otherwise.
-- CAVEAT: that is the vendored crate. Which implementation the deployed validator runs is not
-- pinned by anything in this repository. That gap is precisely what "trusted" means here.
import code_model.hand_written.Curve
open Aeneas Aeneas.Std Result

/-- Bytes `off .. off + m` of a byte array, as a fixed-size array. Pure vocabulary. -/
def curve_shim.bytesAt {n : Usize} (a : Array Std.U8 n) (off : ℕ) (m : Usize)
    (h : off + m.val ≤ n.val) : Array Std.U8 m :=
  ⟨(a.val.drop off).take m.val, by
    have ha := a.property
    simp only [List.length_take, List.length_drop, ha]
    omega⟩

/-- A byte array read as a big-endian natural number. Pure vocabulary. -/
def curve_shim.natOfBE {n : Usize} (b : Array Std.U8 n) : ℕ :=
  b.val.foldl (fun acc byte => acc * 256 + byte.val) 0

/-- What the three alt_bn128 syscalls promise when they succeed -- not that they succeed -- for any `G1`, `G2`, `GT`
    with the structure below. See the file header for where each promise comes from.

    `G1` is a commutative monoid, so `k • P` means P added to itself k times -- which is what
    scalar multiplication is. `GT` only needs a commutative multiplication and a 1. -/
class curve_shim.AltBn128Syscalls (G1 G2 GT : Type) [AddCommMonoid G1] [CommMonoid GT] where
  /-- The pairing the syscall computes. A plain function: no bilinearity is assumed. -/
  pairing : G1 → G2 → GT
  /-- How the syscalls read a 64-byte big-endian G1 point. -/
  decodeG1 : Array Std.U8 64#usize → Option G1
  /-- How the pairing syscall reads a 128-byte big-endian G2 point. -/
  decodeG2 : Array Std.U8 128#usize → Option G2
  /-- Multiplication: if it returned a result, its input point decoded to some P, and the result
      decodes to k·P, where k is the big-endian integer in the last 32 input bytes. -/
  mul_spec : ∀ (input : Array Std.U8 96#usize) (out : Array Std.U8 64#usize),
    curve_shim.alt_bn128_multiplication_shim input = ok (some out) →
    ∃ P : G1,
      decodeG1 (curve_shim.bytesAt input 0 64#usize (by scalar_tac)) = some P ∧
      decodeG1 out =
        some (curve_shim.natOfBE (curve_shim.bytesAt input 64 32#usize (by scalar_tac)) • P)
  /-- Addition: if it returned a result, both input halves decoded to points P and Q, and the
      result decodes to P + Q. -/
  add_spec : ∀ (input : Array Std.U8 128#usize) (out : Array Std.U8 64#usize),
    curve_shim.alt_bn128_addition_shim input = ok (some out) →
    ∃ P Q : G1,
      decodeG1 (curve_shim.bytesAt input 0 64#usize (by scalar_tac)) = some P ∧
      decodeG1 (curve_shim.bytesAt input 64 64#usize (by scalar_tac)) = some Q ∧
      decodeG1 out = some (P + Q)
  /-- Pairing: if it returned a result whose last byte is 1, all four (G1, G2) pairs decoded, and
      the product of their pairings is 1. Pairs sit at offsets 0, 192, 384 and 576, each a 64-byte
      G1 point followed by a 128-byte G2 point. -/
  pairing_spec : ∀ (input : Array Std.U8 768#usize) (out : Array Std.U8 32#usize),
    curve_shim.alt_bn128_pairing_shim input = ok (some out) →
    out.val[31]! = 1#u8 →
    ∃ (P₁ P₂ P₃ P₄ : G1) (Q₁ Q₂ Q₃ Q₄ : G2),
      decodeG1 (curve_shim.bytesAt input 0 64#usize (by scalar_tac)) = some P₁ ∧
      decodeG2 (curve_shim.bytesAt input 64 128#usize (by scalar_tac)) = some Q₁ ∧
      decodeG1 (curve_shim.bytesAt input 192 64#usize (by scalar_tac)) = some P₂ ∧
      decodeG2 (curve_shim.bytesAt input 256 128#usize (by scalar_tac)) = some Q₂ ∧
      decodeG1 (curve_shim.bytesAt input 384 64#usize (by scalar_tac)) = some P₃ ∧
      decodeG2 (curve_shim.bytesAt input 448 128#usize (by scalar_tac)) = some Q₃ ∧
      decodeG1 (curve_shim.bytesAt input 576 64#usize (by scalar_tac)) = some P₄ ∧
      decodeG2 (curve_shim.bytesAt input 640 128#usize (by scalar_tac)) = some Q₄ ∧
      pairing P₁ Q₁ * pairing P₂ Q₂ * pairing P₃ Q₃ * pairing P₄ Q₄ = 1
