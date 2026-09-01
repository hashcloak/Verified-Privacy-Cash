// --- Lean model: BN254 curve / group-operation shim ---
// EXTRACTION-ONLY. Not part of the program's real logic; nothing here is ever
// executed. Same technique and rationale as `fr_shim.rs` (read that first) --
// see MODEL_REPORT.md's "Why the shims are needed".
//
// Why this exists: Charon translates the real `verify_proof` fine, but Aeneas
// cannot. It fails on ark-ff's `Field` trait (GATs, ark-ff-0.5.0/src/fields/mod.rs:159)
// and on `num_bigint`'s `PartialEq for BigUint` (num-bigint-0.4.6/src/biguint.rs:64).
// Marking those crates `--opaque` does NOT help: `--opaque` suppresses function
// *bodies*, but the arkworks types stay in the *signatures* of the code we want,
// so Aeneas drops the bodies of `verify_proof`/`prepare_inputs` instead. Confirmed
// across 6 flag combinations (plain, --monomorphize, --opaque ark_*, + solana_bn254,
// --exclude ark_ff::fields::Field, --exclude all ark/num_bigint). The only technique
// that works is replacing the offending TYPES at the Rust level, which is this file.
//
// Exactly four call sites in zkcash pull arkworks/num-bigint into the model:
//   utils.rs:262      G1::deserialize_with_mode   -> G1Shim::deserialize_uncompressed
//   utils.rs:273,280  g1_point.neg()              -> G1Shim::negate
//   utils.rs:275,282  Fq::serialize_with_mode     -> G1Shim::to_bytes (folds x and y)
//   groth16.rs:150-1  BigUint cmp vs Fr::MODULUS  -> fr_lt_modulus_be
//
// The three `alt_bn128_*` wrappers below are NOT needed to make extraction work --
// solana-bn254's own functions already arrive as opaque foreign items taking and
// returning plain bytes. They are here for the Lean side: the real signatures are
// `&[u8] -> Result<Vec<u8>, AltBn128Error>`, so every downstream proof would carry
// "and the output is 64 bytes long" obligations. Every one of these is fixed-size
// for this circuit, so putting the lengths in the types removes that entirely.
//
// NB: on-chain these three ARE Solana syscalls (`sol_alt_bn128_group_op`), executed
// natively by the validator. Whatever is written for them in Lean is therefore an
// ASSUMPTION about the runtime that no tool in this pipeline can check -- prefer the
// shortest statement that is obviously right over a detailed reimplementation.
//
// Kept in its own module so the whole thing can be marked `--opaque` in one shot;
// Charon's name-matcher does not reliably match individual methods on a local struct.

// --- The verifying key, re-exposed as plain arrays ---
//
// `VERIFYING_KEY` (utils.rs) has type `Groth16Verifyingkey`, which carries a lifetime and
// a `vk_ic: &[[u8; 64]]` slice. Two problems for the model, neither a defect in the real
// type: slice accesses would add a bounds-check failure path everywhere, and Aeneas
// rejects projecting a field out of that struct global ("Unimplemented") -- both at a
// call site and inside a `const` initializer, so a bare `const` alias in utils.rs is not
// enough. They live HERE because this module is already `--opaque`, which stops Aeneas
// looking at the initializers at all, and because they are BN254 curve data: alpha is a
// G1 point, beta/gamma/delta are G2 points, and vk_ic is 8 G1 points.
//
// Consequence to be aware of: the model does NOT know these byte values -- they arrive in
// Lean as uninterpreted constants of the right type. That is enough to state "verified
// against THE verifying key" and to tie the transact model to a single fixed key, but a
// theorem cannot depend on what the key actually is.
//
// Derived from `VERIFYING_KEY` by const-eval rather than copied, so they cannot drift.
// `vk_ic`'s length is 8 (7 public inputs + 1), fixed by the circuit. The `GAMME`
// spelling follows the field name in `Groth16Verifyingkey`.
pub const FV_VK_ALPHA_G1: [u8; 64] = crate::utils::VERIFYING_KEY.vk_alpha_g1;
pub const FV_VK_BETA_G2: [u8; 128] = crate::utils::VERIFYING_KEY.vk_beta_g2;
pub const FV_VK_GAMME_G2: [u8; 128] = crate::utils::VERIFYING_KEY.vk_gamme_g2;
pub const FV_VK_DELTA_G2: [u8; 128] = crate::utils::VERIFYING_KEY.vk_delta_g2;
pub const FV_VK_IC: [[u8; 64]; 8] = [
    crate::utils::VERIFYING_KEY.vk_ic[0],
    crate::utils::VERIFYING_KEY.vk_ic[1],
    crate::utils::VERIFYING_KEY.vk_ic[2],
    crate::utils::VERIFYING_KEY.vk_ic[3],
    crate::utils::VERIFYING_KEY.vk_ic[4],
    crate::utils::VERIFYING_KEY.vk_ic[5],
    crate::utils::VERIFYING_KEY.vk_ic[6],
    crate::utils::VERIFYING_KEY.vk_ic[7],
];

/// A point on the BN254 G1 curve, as the 64-byte uncompressed `x‖y` encoding that
/// ark-serialize produces (little-endian limbs, 32 bytes each). Stand-in for
/// `ark_bn254::g1::G1Affine`.
pub struct G1Shim(pub [u8; 64]);

impl G1Shim {
    /// `G1::deserialize_with_mode(bytes, Compress::No, Validate::Yes)`.
    ///
    /// The real call is handed 65 bytes: the 64-byte point followed by a zero
    /// "infinity flag" byte (the `&[0u8][..]` tail of the `concat` at utils.rs:263).
    /// That byte is constant, so it is dropped here rather than modelled.
    /// `None` corresponds to the real `Err(_)` (bad encoding, or a point that is not
    /// on the curve / not in the correct subgroup -- `Validate::Yes`).
    pub fn deserialize_uncompressed(_bytes: &[u8; 64]) -> Option<G1Shim> {
        unimplemented!()
    }

    /// Curve-point negation, `-P`. Stand-in for `<G1Affine as Neg>::neg`.
    pub fn negate(self) -> G1Shim {
        unimplemented!()
    }

    /// Serializes `x` then `y`, each `Fq::serialize_with_mode(.., Compress::No)`.
    /// The original writes them into `proof_a_neg[..32]` and `proof_a_neg[32..]`
    /// separately and treats a failure of either as `return false`; both are
    /// infallible for an in-range field element, so this folds them into one op.
    pub fn to_bytes(&self) -> [u8; 64] {
        unimplemented!()
    }
}

/// `groth16::is_less_than_bn254_field_size_be`: interprets the 32 bytes as a
/// BIG-ENDIAN integer and reports whether it is `< r`, the BN254 scalar-field
/// modulus (`ark_bn254::Fr::MODULUS`).
///
/// This is a real security check, not a formality: it is what stops a caller
/// supplying a public input that is congruent to, but not equal to, the intended
/// value. Worth stating as its own named assumption in `FunsExternal.lean`.
pub fn fr_lt_modulus_be(_bytes: &[u8; 32]) -> bool {
    unimplemented!()
}

/// `alt_bn128_multiplication`: input is a 64-byte G1 point followed by a 32-byte
/// scalar; output is the 64-byte encoding of `[k]P`. `None` = the real `Err(_)`.
pub fn alt_bn128_multiplication_shim(_input: &[u8; 96]) -> Option<[u8; 64]> {
    unimplemented!()
}

/// `alt_bn128_addition`: input is two 64-byte G1 points; output is the 64-byte
/// encoding of their sum. `None` = the real `Err(_)`.
pub fn alt_bn128_addition_shim(_input: &[u8; 128]) -> Option<[u8; 64]> {
    unimplemented!()
}

/// `alt_bn128_pairing`: input is a whole number of (G1, G2) pairs, 192 bytes each.
/// For this verifying key it is always exactly 4 pairs = 768 bytes. Output is a
/// 32-byte big-endian value that is 1 iff the pairing product is the identity in
/// the target group. `None` = the real `Err(_)`.
pub fn alt_bn128_pairing_shim(_input: &[u8; 768]) -> Option<[u8; 32]> {
    unimplemented!()
}
