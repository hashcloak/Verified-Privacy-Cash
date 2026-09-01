// --- Lean model: Fr shim ---
// Aeneas cannot currently translate ark-bn254/ark-ff's real Fr type (const-generic
// BigInt<N> + mutually-recursive Field/PrimeField/AdditiveGroup/FftField traits --
// see MODEL_REPORT.md's "Why the shims are needed"). This is a structurally
// simple stand-in exposing the same operations check_public_amount/transact actually
// use, so Aeneas can see something shaped like `solana_pubkey::Pubkey` (which already
// extracts cleanly) instead of the real Fr.
//
// Kept in its own module (rather than inline in utils.rs) so the whole module can be
// marked `--opaque` in one shot -- Charon's name-matcher doesn't reliably match
// individual inherent/trait-impl methods on a local struct, but whole-module opacity
// is confirmed to work. With the module opaque, Aeneas emits these as `axiom`
// declarations (in FunsExternal_Template.lean) instead of inlining the
// `unimplemented!()` bodies as `fail panic`, so they can be given real definitions
// stating what these operations actually compute. Done for the check_public_amount
// model (CheckPublicAmountShim/FunsExternal.lean defines FrShim as `ZMod bn254_r`);
// still bare signatures in TransactShim. NOT part of the program's real logic.
#[derive(Clone, Copy, PartialEq)]
pub struct FrShim(pub [u8; 32]);

impl FrShim {
    pub fn from_u64(_x: u64) -> Self { unimplemented!() }
    pub fn from_be_bytes_mod_order(_bytes: &[u8; 32]) -> Self { unimplemented!() }
    pub fn from_le_bytes_mod_order(_bytes: &[u8; 32]) -> Self { unimplemented!() }
}
impl core::ops::Add for FrShim {
    type Output = Self;
    fn add(self, _other: Self) -> Self { unimplemented!() }
}
impl core::ops::Sub for FrShim {
    type Output = Self;
    fn sub(self, _other: Self) -> Self { unimplemented!() }
}
impl core::ops::Neg for FrShim {
    type Output = Self;
    fn neg(self) -> Self { unimplemented!() }
}
impl PartialOrd for FrShim {
    fn partial_cmp(&self, _other: &Self) -> Option<core::cmp::Ordering> { unimplemented!() }
}
