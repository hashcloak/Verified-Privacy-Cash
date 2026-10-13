//! The crypto answers a `transact` scenario needs, for the Lean model.
//!
//! The model takes Poseidon, SHA-256 and the `alt_bn128` syscalls as
//! parameters. To run it on a scenario it is given, for each call the program
//! makes, the answer: this module runs the extracted `zkcash_core::transact`
//! on the host on the same accounts and arguments, with the primitives the
//! program uses (light-hasher's Poseidon, SHA-256, solana-bn254's alt_bn128)
//! wrapped to record every (input, output). The model then looks answers up
//! in those tables; a call it makes that is not in them fails the scenario.
//! G1 negation is not recorded: the model computes it itself (Bn254.lean).
//!
//! The host run only produces the tables. Its runtime always succeeds, so it
//! makes at least the calls the real run makes (extra entries are unused).

use std::cell::RefCell;
use zkcash_core::admin::GlobalConfig;
use zkcash_core::merkle_tree::MerkleTreeAccount;
use zkcash_core::transact::{Proof, ProofVerifier, SolRuntime};

/// The recorded calls, each as (input, output); `None` is a failed call.
#[derive(Default, Clone)]
pub struct Tables {
    pub poseidon: Vec<([u8; 32], [u8; 32], [u8; 32])>,
    pub sha256: Vec<(Vec<u8>, [u8; 32])>,
    pub multiplication: Vec<(Vec<u8>, Option<[u8; 64]>)>,
    pub addition: Vec<(Vec<u8>, Option<[u8; 64]>)>,
    pub pairing: Vec<(Vec<u8>, Option<[u8; 32]>)>,
}

thread_local! {
    static LOG: RefCell<Tables> = RefCell::new(Tables::default());
}

fn record(f: impl FnOnce(&mut Tables)) {
    LOG.with(|l| f(&mut l.borrow_mut()));
}

struct RecHasher;

impl zkcash_core::merkle_tree::Hasher for RecHasher {
    fn hash_pair(left: &[u8; 32], right: &[u8; 32]) -> [u8; 32] {
        use light_hasher::Hasher;
        let out = light_hasher::Poseidon::hashv(&[left.as_slice(), right.as_slice()]).unwrap();
        record(|t| t.poseidon.push((*left, *right, out)));
        out
    }

    fn zero_bytes() -> [[u8; 32]; zkcash_core::merkle_tree::ZERO_BYTES_LEN] {
        zero_bytes()
    }
}

/// The program's `zero_bytes` (light-hasher's Poseidon empty-subtree roots).
pub fn zero_bytes() -> [[u8; 32]; zkcash_core::merkle_tree::ZERO_BYTES_LEN] {
    use light_hasher::Hasher;
    light_hasher::Poseidon::zero_bytes()
}

struct RecSha256;

impl zkcash_core::ext_data::Sha256 for RecSha256 {
    fn hash(data: &[u8]) -> [u8; 32] {
        use sha2::Digest;
        let out: [u8; 32] = sha2::Sha256::digest(data).into();
        record(|t| t.sha256.push((data.to_vec(), out)));
        out
    }
}

struct RecBn254;

impl zkcash_core::groth16::Bn254 for RecBn254 {
    fn g1_mul(point: &[u8; 64], scalar: &[u8; 32]) -> Option<[u8; 64]> {
        let input = [&point[..], &scalar[..]].concat();
        let out = solana_bn254::prelude::alt_bn128_multiplication(&input).ok().and_then(|v| v.try_into().ok());
        record(|t| t.multiplication.push((input, out)));
        out
    }

    fn g1_add(a: &[u8; 64], b: &[u8; 64]) -> Option<[u8; 64]> {
        let input = [&a[..], &b[..]].concat();
        let out = solana_bn254::prelude::alt_bn128_addition(&input).ok().and_then(|v| v.try_into().ok());
        record(|t| t.addition.push((input, out)));
        out
    }

    fn pairing(input: &[u8; 768]) -> Option<[u8; 32]> {
        let out = solana_bn254::prelude::alt_bn128_pairing(input).ok().and_then(|v| v.try_into().ok());
        record(|t| t.pairing.push((input.to_vec(), out)));
        out
    }

    /// The program's `SolanaBn254::negate_g1` (utils.rs), not recorded.
    fn negate_g1(proof_a: &[u8; 64]) -> Option<[u8; 64]> {
        use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, Validate};
        use std::ops::Neg;
        let g1 = ark_bn254::g1::G1Affine::deserialize_with_mode(
            &*[&change_endianness(&proof_a[..]), &[0u8][..]].concat(),
            Compress::No,
            Validate::Yes,
        )
        .ok()?;
        let mut neg = [0u8; 65];
        g1.neg().x.serialize_with_mode(&mut neg[..32], Compress::No).ok()?;
        g1.neg().y.serialize_with_mode(&mut neg[32..], Compress::No).ok()?;
        change_endianness(&neg[..64]).try_into().ok()
    }
}

fn change_endianness(bytes: &[u8]) -> Vec<u8> {
    bytes.chunks(32).flat_map(|c| c.iter().rev().copied()).collect()
}

#[derive(Clone, Copy)]
struct ArkFr(ark_bn254::Fr);

impl zkcash_core::field::PrimeField for ArkFr {
    fn from_u64(x: u64) -> Self {
        ArkFr(ark_bn254::Fr::from(x))
    }
    fn from_be_bytes_mod_order(bytes: &[u8; 32]) -> Self {
        use ark_ff::PrimeField;
        ArkFr(ark_bn254::Fr::from_be_bytes_mod_order(bytes))
    }
    fn from_le_bytes_mod_order(bytes: &[u8; 32]) -> Self {
        use ark_ff::PrimeField;
        ArkFr(ark_bn254::Fr::from_le_bytes_mod_order(bytes))
    }
    fn add(a: Self, b: Self) -> Self {
        ArkFr(a.0 + b.0)
    }
    fn sub(a: Self, b: Self) -> Self {
        ArkFr(a.0 - b.0)
    }
    fn neg(a: Self) -> Self {
        ArkFr(-a.0)
    }
    fn le(a: Self, b: Self) -> bool {
        a.0 <= b.0
    }
    fn eq(a: Self, b: Self) -> bool {
        a.0 == b.0
    }
}

struct RecVerifier;

impl ProofVerifier for RecVerifier {
    fn verify(proof: &Proof) -> bool {
        zkcash_core::groth16::verify_proof::<RecBn254>(proof, &zkcash_core::verifying_key::VERIFYING_KEY)
    }
}

/// A runtime on which every call succeeds.
struct Ample;

impl SolRuntime for Ample {
    fn rent_exempt_minimum(&mut self) -> Result<u64, ()> {
        Ok(0)
    }
    fn transfer_from_signer_to_tree_token(&mut self, _: u64) -> Result<(), ()> {
        Ok(())
    }
    fn tree_token_lamports(&self) -> u64 {
        u64::MAX / 2
    }
    fn recipient_lamports(&self) -> u64 {
        0
    }
    fn fee_recipient_lamports(&self) -> u64 {
        0
    }
    fn set_tree_token_lamports(&mut self, _: u64) -> Result<(), ()> {
        Ok(())
    }
    fn set_recipient_lamports(&mut self, _: u64) -> Result<(), ()> {
        Ok(())
    }
    fn set_fee_recipient_lamports(&mut self, _: u64) -> Result<(), ()> {
        Ok(())
    }
}

/// Runs `transact` on the host and returns every crypto call it made.
#[allow(clippy::too_many_arguments)]
pub fn tables(
    mut tree: MerkleTreeAccount,
    config: GlobalConfig,
    proof: &Proof,
    ext_amount: i64,
    fee: u64,
    recipient: [u8; 32],
    fee_recipient: [u8; 32],
    out1: &[u8],
    out2: &[u8],
) -> Tables {
    LOG.with(|l| *l.borrow_mut() = Tables::default());
    let _ = zkcash_core::transact::transact::<RecHasher, ArkFr, RecSha256, RecVerifier, Ample>(
        &mut Ample, &mut tree, &config, proof, ext_amount, fee, recipient, fee_recipient, out1, out2,
    );
    LOG.with(|l| l.borrow().clone())
}
