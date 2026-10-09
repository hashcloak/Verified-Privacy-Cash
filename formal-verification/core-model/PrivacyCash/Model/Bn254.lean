/-
The BN254 curve operations behind the Groth16 verifier: the program's
`SolanaBn254` (`programs/zkcash/src/utils.rs`), which implements the
extracted `zkcash_core::groth16::Bn254` trait.

Its four methods are of two kinds:

* `g1_mul`, `g1_add`, `pairing` call the `alt_bn128` syscalls, which the
  validator executes. Lean never sees their code, so they are parameters
  (`AltBn128`), and what a successful answer means is a hypothesis a theorem
  takes (`AltBn128Contracts`), never an axiom.
* `negate_g1` is arkworks code compiled into the program itself. It is
  DEFINED here, mirroring arkworks 0.5.0 (the version the program builds
  against) step by step: decode the point, negate it, encode it.

The G1 definitions (`bn254_q`, `G1Affine`, `deserializeUncompressed`, `neg`,
`toBytes`) and the shape of the syscall contracts are taken from
Verified-Privacy-Cash's `code_model/hand_written/{Curve,SyscallContracts}.lean`,
where each rule cites the arkworks / solana-bn254 source it comes from.
-/
import PrivacyCash.Model.Basic
import Mathlib.Data.ZMod.Basic
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Model

/-! ## G1 points, as arkworks represents them -/

/-- BN254 base field modulus q, the field of G1 coordinates
    (`ark_bn254::Fq::MODULUS`). Not the scalar field modulus r. -/
def bn254BaseModulus : Nat :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- arkworks' `Affine<ark_bn254::g1::Config>`: two coordinates and the
    infinity flag. Not every value is on the curve; `deserializeUncompressed`
    only produces points that are (or the identity). -/
structure G1Affine where
  x : ZMod bn254BaseModulus
  y : ZMod bn254BaseModulus
  infinity : Bool

/-- Bytes read as a little-endian number, least significant byte first. -/
def leNatOfList (l : List U8) : Nat := l.foldr (fun b acc => b.val + 256 * acc) 0

/-- `n` as 32 little-endian bytes (exact for n < 2^256). -/
def leBytes32 (n : Nat) : List U8 :=
  (List.range 32).map fun i => U8.ofNatCore (n / 256 ^ i % 256) (by
    have : n / 256 ^ i % 256 < 256 := Nat.mod_lt _ (by norm_num)
    simp only [UScalarTy.numBits]; omega)

/-- `G1Affine::deserialize_with_mode(bytes, Compress::No, Validate::Yes)`
    (ark-ec 0.5.0, short_weierstrass): `x` is bytes 0..31 little-endian and
    must be < q; the top two bits of byte 63 are flags (bit 6 infinity, bit 7
    y-negative, both set is rejected), cleared before reading `y` from bytes
    32..63, which must be < q. With the infinity flag the result is the
    identity; otherwise the point must satisfy y² = x³ + 3. No subgroup check
    is needed: G1 has cofactor 1. The caller passes a 65th byte (0) that
    arkworks never reads for an uncompressed BN254 point, so it is omitted. -/
def deserializeUncompressed (bytes : Std.Array U8 64#usize) : Option G1Affine :=
  let l := bytes.val
  let top := (l.getD 63 0#u8).val
  let isNeg : Bool := top / 128 % 2 == 1
  let isInf : Bool := top / 64 % 2 == 1
  let xn := leNatOfList (l.take 32)
  let yn := leNatOfList ((l.drop 32).take 31) + (top % 64) * 256 ^ 31
  if isNeg && isInf then none
  else if bn254BaseModulus ≤ xn then none
  else if bn254BaseModulus ≤ yn then none
  else if isInf then some ⟨0, 0, true⟩
  else
    let x : ZMod bn254BaseModulus := xn
    let y : ZMod bn254BaseModulus := yn
    if y ^ 2 = x ^ 3 + 3 then some ⟨x, y, false⟩ else none

/-- `impl Neg for Affine` (ark-ec 0.5.0): negate y, keep x and the flag. -/
def G1Affine.neg (p : G1Affine) : G1Affine := { p with y := -p.y }

/-- How `negate_g1` writes the point out: `x` then `y`, each serialized on its
    own as its canonical value in 32 little-endian bytes, without flags. -/
def G1Affine.toBytes (p : G1Affine) : Std.Array U8 64#usize :=
  Std.Array.from (leBytes32 p.x.val ++ leBytes32 p.y.val) (by simp [leBytes32])

/-- A `Vec` of exactly 64 bytes as an array (`try_into::<[u8; 64]>`). -/
def toArray64 (v : alloc.vec.Vec U8) : Option (Std.Array U8 64#usize) :=
  if h : v.val.length = 64 then some (Std.Array.from v.val (by simpa using h)) else none

/-- `SolanaBn254::negate_g1`: reverse each 32-byte half (big-endian to
    arkworks' little-endian), decode and validate the point, negate it, encode
    it, and reverse the halves back. `change_endianness` is the extracted
    `zkcash_core` one, which the program's `utils::change_endianness` calls
    (checked against upstream by `tests/differential/byte_helpers.rs`; the
    whole function by `Tests/Bn254Vectors.lean`). Serializing a coordinate into a 32-byte buffer cannot
    fail, so the two `is_err` branches are unreachable and not modelled. -/
def negateG1 (proofA : Std.Array U8 64#usize) : Result (Option (Std.Array U8 64#usize)) := do
  let le ← zkcash_core.utils.change_endianness (Std.Array.to_slice proofA)
  match toArray64 le >>= deserializeUncompressed with
  | none => ok none
  | some p =>
    let out ← zkcash_core.utils.change_endianness (Std.Array.to_slice p.neg.toBytes)
    ok (toArray64 out)

/-! ## The `alt_bn128` syscalls -/

/-- The three syscalls, as `SolanaBn254` calls them: the input bytes in, and
    `None` if the syscall fails or its output is not the expected length
    (`.ok()?.try_into().ok()`). -/
structure AltBn128 where
  /-- `alt_bn128_multiplication(point ‖ scalar)`. -/
  multiplication : Std.Array U8 96#usize → Option (Std.Array U8 64#usize)
  /-- `alt_bn128_addition(a ‖ b)`. -/
  addition : Std.Array U8 128#usize → Option (Std.Array U8 64#usize)
  /-- `alt_bn128_pairing(input)`. -/
  pairing : Std.Array U8 768#usize → Option (Std.Array U8 32#usize)

/-- `a ‖ b` as a fixed-size array. -/
def concatArrays {m n k : Usize} (a : Std.Array U8 m) (b : Std.Array U8 n)
    (h : m.val + n.val = k.val) : Std.Array U8 k :=
  Std.Array.from (a.val ++ b.val) (by simp [h])

/-- The program's `SolanaBn254`, as the extracted `Bn254` trait. -/
def solanaBn254 (s : AltBn128) : zkcash_core.groth16.Bn254 Unit where
  g1_mul p k := ok (s.multiplication (concatArrays p k (by simp)))
  g1_add a b := ok (s.addition (concatArrays a b (by simp)))
  pairing input := ok (s.pairing input)
  negate_g1 := negateG1

/-- Bytes `off .. off + m` of an array. -/
def bytesAt {n : Usize} (a : Std.Array U8 n) (off : Nat) (m : Usize)
    (h : off + m.val ≤ n.val) : Std.Array U8 m :=
  Std.Array.from ((a.val.drop off).take m.val) (by simp; omega)

/-- Bytes read as a big-endian number. -/
def beNatOf {n : Usize} (b : Std.Array U8 n) : Nat := b.val.foldl (fun acc x => acc * 256 + x.val) 0

/-- **Hypothesis (the syscalls are correct, soundness direction):** what a
    successful syscall answer means, for some groups `G1`, `G2`, `GT`, decoders
    and pairing. Only "if it answered, this is what it computed"; nothing about
    when it fails. Bilinearity is deliberately not assumed: the code only
    checks that four pairings multiply to 1. (Source: solana-bn254's native
    implementation; which implementation the deployed validator runs is
    exactly what is trusted here.) -/
structure AltBn128Contracts (s : AltBn128) (G1 G2 GT : Type) [AddCommMonoid G1] [CommMonoid GT] where
  /-- The pairing the syscall computes. -/
  e : G1 → G2 → GT
  /-- How the syscalls read a 64-byte big-endian G1 point. -/
  decodeG1 : Std.Array U8 64#usize → Option G1
  /-- How the pairing syscall reads a 128-byte big-endian G2 point. -/
  decodeG2 : Std.Array U8 128#usize → Option G2
  /-- Multiplication returns k·P for the point P in bytes 0..63 and the
      big-endian integer k in bytes 64..95 (unreduced). -/
  mul : ∀ input out, s.multiplication input = some out →
    ∃ P : G1, decodeG1 (bytesAt input 0 64#usize (by simp)) = some P ∧
      decodeG1 out = some (beNatOf (bytesAt input 64 32#usize (by simp)) • P)
  /-- Addition returns P + Q. -/
  add : ∀ input out, s.addition input = some out →
    ∃ P Q : G1, decodeG1 (bytesAt input 0 64#usize (by simp)) = some P ∧
      decodeG1 (bytesAt input 64 64#usize (by simp)) = some Q ∧
      decodeG1 out = some (P + Q)
  /-- A pairing answer ending in 1 means the four (G1, G2) pairs at offsets
      0, 192, 384, 576 decode and their pairings multiply to 1. -/
  pairing : ∀ input out, s.pairing input = some out → out.val[31]! = 1#u8 →
    ∃ (P₁ P₂ P₃ P₄ : G1) (Q₁ Q₂ Q₃ Q₄ : G2),
      decodeG1 (bytesAt input 0 64#usize (by simp)) = some P₁ ∧
      decodeG2 (bytesAt input 64 128#usize (by simp)) = some Q₁ ∧
      decodeG1 (bytesAt input 192 64#usize (by simp)) = some P₂ ∧
      decodeG2 (bytesAt input 256 128#usize (by simp)) = some Q₂ ∧
      decodeG1 (bytesAt input 384 64#usize (by simp)) = some P₃ ∧
      decodeG2 (bytesAt input 448 128#usize (by simp)) = some Q₃ ∧
      decodeG1 (bytesAt input 576 64#usize (by simp)) = some P₄ ∧
      decodeG2 (bytesAt input 640 128#usize (by simp)) = some Q₄ ∧
      e P₁ Q₁ * e P₂ Q₂ * e P₃ Q₃ * e P₄ Q₄ = 1

/-- The contracts can be met (so assuming them is never vacuous by
    contradiction): syscalls that always fail satisfy them trivially. -/
theorem altBn128Contracts_satisfiable :
    Nonempty (AltBn128Contracts ⟨fun _ => none, fun _ => none, fun _ => none⟩ Unit Unit Unit) :=
  ⟨{ e := fun _ _ => (), decodeG1 := fun _ => none, decodeG2 := fun _ => none
     mul := by simp, add := by simp, pairing := by simp }⟩

end PrivacyCash.Model
