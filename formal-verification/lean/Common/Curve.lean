-- SHARED trusted base: the BN254 curve surface.
--
-- Previously duplicated between TransactShim/FunsExternal.lean and
-- VerifyProofShim/FunsExternal.lean, with a "KEEP THEM IN SYNC" comment on each copy.
-- That comment understated the problem: `curve_shim.G1Shim` was declared as a separate
-- `axiom : Type` in each library, so the two were DIFFERENT TYPES even when the text
-- matched, and no fact proved about one transferred to the other. Declaring it once
-- here is what actually makes VerifyProofShim a sub-model of TransactShim rather than
-- an unrelated universe that happens to look similar.
--
--   DERIVED  1  fr_lt_modulus_be -- plain integer arithmetic, so it is reproduced.
--   TRUSTED  7  the G1 type and the BN254 group operations.
--
-- NOTE on the six trusted operations: only the three `alt_bn128_*` are Solana syscalls.
-- `deserialize_uncompressed`, `negate` and `to_bytes` are arkworks code compiled into
-- the BPF program itself -- plain field arithmetic that COULD be given real definitions
-- via Mathlib's `WeierstrassCurve.Affine.Point` over `ZMod q` (`y² = x³ + 3`, cofactor 1).
-- See MODEL_COVERAGE.md section 2.
import Common.Bn254
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-- TRUSTED (CURVE). [zkcash::curve_shim::G1Shim]: a point on the BN254 G1 curve.
    Deliberately abstract rather than `Array U8 64`. The Rust shim wraps 64 bytes, but not
    every 64-byte string is a valid curve point -- `deserialize_uncompressed` performs
    subgroup and on-curve validation (`Validate::Yes`). Keeping the type abstract stops a
    proof from silently assuming an arbitrary byte string is a group element.
    Source: 'programs/zkcash/src/curve_shim.rs', lines 74:0-74:32 -/
axiom curve_shim.G1Shim : Type

-- TRUSTED (CURVE). Decodes 64 bytes to a G1 point, REJECTING points that are off-curve or
-- outside the prime-order subgroup (the real call passes `Validate::Yes`). `none` is that
-- rejection; a statement of this axiom must not drop the validation.
/-- [zkcash::curve_shim::{zkcash::curve_shim::G1Shim}::deserialize_uncompressed]:
    Source: 'programs/zkcash/src/curve_shim.rs', lines 84:4-86:5
    Visibility: public -/
axiom curve_shim.G1Shim.deserialize_uncompressed
  : Array Std.U8 64#usize → Result (Option curve_shim.G1Shim)

-- TRUSTED (CURVE). Group negation `-P`.
/-- [zkcash::curve_shim::{zkcash::curve_shim::G1Shim}::negate]:
    Source: 'programs/zkcash/src/curve_shim.rs', lines 89:4-91:5
    Visibility: public -/
axiom curve_shim.G1Shim.negate : curve_shim.G1Shim → Result curve_shim.G1Shim

-- TRUSTED (CURVE). Encodes x‖y, 32 bytes each. Inverse of deserialize on valid points.
/-- [zkcash::curve_shim::{zkcash::curve_shim::G1Shim}::to_bytes]:
    Source: 'programs/zkcash/src/curve_shim.rs', lines 97:4-99:5
    Visibility: public -/
axiom curve_shim.G1Shim.to_bytes
  : curve_shim.G1Shim → Result (Array Std.U8 64#usize)

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
