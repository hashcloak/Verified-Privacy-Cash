-- SHARED trusted base: the BN254 curve surface.
--
-- Previously duplicated between TransactShim/FunsExternal.lean and
-- VerifyProofShim/FunsExternal.lean, with a "KEEP THEM IN SYNC" comment on each copy.
-- That comment understated the problem: `curve_shim.G1Shim` was declared as a separate
-- `axiom : Type` in each library, so the two were DIFFERENT TYPES even when the text
-- matched, and no fact proved about one transferred to the other. Declaring it once
-- here gives both models ONE curve surface. (The models still cannot be imported
-- together -- their generated code overlaps; see MODEL_COVERAGE.md.)
--
--   DERIVED  4  the G1Shim type, deserialize_uncompressed, negate, to_bytes -- defined to
--               mirror arkworks 0.5.0 exactly -- plus fr_lt_modulus_be.
--   TRUSTED  3  the alt_bn128 addition, multiplication and pairing syscalls.
--
-- NOTE: only the three `alt_bn128_*` operations are Solana syscalls, executed by the
-- validator, so they stay axioms. `deserialize_uncompressed`, `negate` and `to_bytes` are
-- arkworks code compiled into the BPF program itself; they are defined below to mirror
-- arkworks 0.5.0 directly rather than via Mathlib's `WeierstrassCurve.Affine.Point`. That
-- keeps them faithful to the deployed bytes (flag bits, canonical-encoding checks, the
-- infinity path), at the cost of not yet carrying Mathlib's group-law theorems.
import code_model.hand_written.Bn254
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-! ## G1 points — DERIVED

`G1Shim` and the three operations below were axioms. They are now defined to mirror arkworks
0.5.0 byte for byte: the exact version zkcash builds against (ark-bn254 / ark-ec / ark-ff /
ark-serialize 0.5.0). Each rule cites its source under formal-verification/vendor/. -/

/-- DERIVED. BN254 base field modulus `q`: the field the G1 coordinates live in.
    Not `bn254_r`, which is the scalar field. Source: vendor/ark-bn254/src/fields/fq.rs:4 -/
def curve_shim.bn254_q : ℕ :=
  21888242871839275222246405745257275088696311157297823662689037894645226208583

/-- DERIVED. [zkcash::curve_shim::G1Shim], defined as arkworks' `Affine<ark_bn254::g1::Config>`:
    two coordinates in 𝔽_q plus the infinity flag, the same three fields as
    `pub struct Affine<P: SWCurveConfig> { x, y, infinity }` (vendor/ark-ec/src/models/
    short_weierstrass/affine.rs:30). Not every value of this type is on the curve;
    `deserialize_uncompressed` is how the model obtains one, and it validates.
    Source: 'programs/zkcash/src/curve_shim.rs', lines 74:0-74:32 -/
structure curve_shim.G1Shim where
  x : ZMod curve_shim.bn254_q
  y : ZMod curve_shim.bn254_q
  infinity : Bool

/-- Little-endian bytes to a natural number, least significant byte first. -/
def curve_shim.leNat (l : List Std.U8) : ℕ :=
  l.foldr (fun b acc => b.val + 256 * acc) 0

/-- The low byte of a natural number. Namespaced because `byteOfNat` already exists in
    TrustedFuns.lean, which imports this file. -/
def curve_shim.lowByte (n : ℕ) : Std.U8 :=
  Std.U8.ofNatCore (n % 256)
    (by have : n % 256 < 256 := Nat.mod_lt _ (by norm_num); simpa using this)

/-- 32-byte little-endian encoding of `n` (exact for n < 2^256). -/
def curve_shim.leBytes32 (n : ℕ) : List Std.U8 :=
  (List.range 32).map (fun i => curve_shim.lowByte (n / 256 ^ i))

/-- DERIVED. `G1::deserialize_with_mode(bytes, Compress::No, Validate::Yes)` for BN254, as
    implemented in ark-ec 0.5.0 (short_weierstrass/mod.rs, `deserialize_with_mode`):

    1. `x` = bytes 0..31, little-endian. Rejected if ≥ q (ark-ff `from_bigint` returns None).
    2. The flags are the top two bits of byte 63 (ark-serialize `from_u8_remove_flags`):
       bit 6 = PointAtInfinity, bit 7 = YIsNegative. Both set is rejected
       (`SWFlags::from_u8`: `(true, true) => None`). The flag bits are cleared, then
       `y` = bytes 32..63, little-endian, rejected if ≥ q.
    3. If the infinity flag is set, the result is the identity `{x = 0, y = 0, infinity}`.
       The decoded x and y are NOT checked against the curve — but they did have to be < q,
       because steps 1 and 2 fail before the infinity check is reached.
    4. Otherwise the point must satisfy y² = x³ + 3 (COEFF_A = 0, COEFF_B = 3). The subgroup
       check always passes: ark-bn254 g1.rs overrides `is_in_correct_subgroup_assuming_on_curve`
       to return `true` (cofactor 1).

    YIsNegative is stripped and otherwise ignored; uncompressed decoding uses only the
    infinity flag.

    The Rust caller passes 65 bytes, with a trailing 0. arkworks 0.5.0 reads exactly 64 for an
    uncompressed BN254 point — 254-bit coordinates, the 2 flag bits packed into y's spare bits —
    and never consumes the 65th, so it is not modelled. That equivalence is specific to this
    arkworks version.
    Source: 'programs/zkcash/src/curve_shim.rs', lines 84:4-86:5 -/
def curve_shim.G1Shim.deserialize_uncompressed (bytes : Array Std.U8 64#usize) :
    Result (Option curve_shim.G1Shim) :=
  let l := bytes.val
  let top := (l.getD 63 0#u8).val
  let isNeg : Bool := top / 128 % 2 == 1
  let isInf : Bool := top / 64 % 2 == 1
  let xn := curve_shim.leNat (l.take 32)
  let yn := curve_shim.leNat ((l.drop 32).take 31) + (top % 64) * 256 ^ 31
  if isNeg && isInf then ok none
  else if curve_shim.bn254_q ≤ xn then ok none
  else if curve_shim.bn254_q ≤ yn then ok none
  else if isInf then ok (some ⟨0, 0, true⟩)
  else
    let x : ZMod curve_shim.bn254_q := xn
    let y : ZMod curve_shim.bn254_q := yn
    if y ^ 2 = x ^ 3 + 3 then ok (some ⟨x, y, false⟩) else ok none

/-- DERIVED. Point negation, as `impl Neg for Affine` in ark-ec 0.5.0 (affine.rs:254):
    `self.y.neg_in_place(); self`. Negates y and keeps x and the infinity flag; the identity
    stays the identity because -0 = 0.
    Source: 'programs/zkcash/src/curve_shim.rs', lines 89:4-91:5 -/
def curve_shim.G1Shim.negate (p : curve_shim.G1Shim) : Result curve_shim.G1Shim :=
  ok { p with y := -p.y }

/-- DERIVED. How `verify_proof` writes the negated point back out: it serializes the two
    COORDINATES separately, `x.serialize_with_mode(..)` then `y.serialize_with_mode(..)`
    (utils.rs) — not the point. ark-ff 0.5.0 writes a field element as its canonical value
    (`into_bigint`) in 32 little-endian bytes, with `EmptyFlags` (fp/mod.rs,
    `serialize_with_flags`). So the output carries no flag bits, and the identity encodes as
    64 zero bytes.
    Source: 'programs/zkcash/src/curve_shim.rs', lines 97:4-99:5 -/
def curve_shim.G1Shim.to_bytes (p : curve_shim.G1Shim) : Result (Array Std.U8 64#usize) :=
  ok ⟨curve_shim.leBytes32 p.x.val ++ curve_shim.leBytes32 p.y.val,
      by simp [curve_shim.leBytes32]⟩

/-- DERIVED. `groth16::is_less_than_bn254_field_size_be`: decode the 32 bytes BIG-ENDIAN and
    compare against `r`. The Rust routes this through `num_bigint::BigUint` (which is what
    Aeneas choked on, hence the shim), but the operation itself is plain integer arithmetic
    with no cryptography in it, so it is reproduced here rather than assumed.
    This is a REAL SECURITY CHECK: it is what stops a caller supplying a public input that is
    congruent to, but not equal to, the intended field element. Deliberately the same
    big-endian decode as `FrShim.from_be_bytes_mod_order` -- relating the two is exactly
    what a proof about public-input canonicity will need.
    Source: 'programs/zkcash/src/curve_shim.rs', lines 109:0-111:1 -/
def curve_shim.fr_lt_modulus_be (bytes : Array Std.U8 32#usize) : Result Bool :=
  ok (decide ((bytes.val.foldl (fun acc byte => acc * 256 + byte.val) 0 : Nat) < bn254_r))

-- TRUSTED (CURVE). Syscall. Input is a 64-byte G1 point followed by a 32-byte scalar;
-- output encodes [k]P.
/-- [zkcash::curve_shim::alt_bn128_multiplication_shim]:
    Source: 'programs/zkcash/src/curve_shim.rs', lines 115:0-117:1
    Visibility: public -/
axiom curve_shim.alt_bn128_multiplication_shim
  : Array Std.U8 96#usize → Result (Option (Array Std.U8 64#usize))

-- TRUSTED (CURVE). Syscall. Input is two 64-byte G1 points; output encodes their sum.
/-- [zkcash::curve_shim::alt_bn128_addition_shim]:
    Source: 'programs/zkcash/src/curve_shim.rs', lines 121:0-123:1
    Visibility: public -/
axiom curve_shim.alt_bn128_addition_shim
  : Array Std.U8 128#usize → Result (Option (Array Std.U8 64#usize))

-- TRUSTED (CURVE). Syscall. 768 bytes = exactly 4 (G1,G2) pairs for this verifying key.
-- Returns 32 bytes whose last byte is 1 iff the pairing product is the identity. THE most
-- consequential assumption in the model: soundness of `transact` reduces to what a `1` here
-- is taken to guarantee. `Groth16.verify` in the spec is the abstract counterpart.
/-- [zkcash::curve_shim::alt_bn128_pairing_shim]:
    Source: 'programs/zkcash/src/curve_shim.rs', lines 129:0-131:1
    Visibility: public -/
axiom curve_shim.alt_bn128_pairing_shim
  : Array Std.U8 768#usize → Result (Option (Array Std.U8 32#usize))
