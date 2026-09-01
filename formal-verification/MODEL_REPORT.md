# Lean model of `zkcash`

What the Charon/Aeneas pipeline extracts from `anchor/programs/zkcash`, what the resulting Lean
model assumes rather than derives, and how it relates to the written spec. `SETUP.md` Part 2
covers the environment; `extract.sh` is the exact procedure and regenerates everything below.

## What is extracted

Three Lean libraries under `lean/`. All three translate without errors and contain no `sorry`,
`admit`, or `fail panic`, and `lake build` typechecks them together with `Spec/`.

| Library | Rust entry point | Contents |
|---|---|---|
| `TransactShim/` | `zkcash::fv_transact_entry` (`lib.rs`) | the `transact` instruction end to end: root check, ext-data-hash check, `check_public_amount`, `validate_fee`, proof verification, both balance-update branches, the fee transfer, and both `MerkleTree::append` calls, in the order the real source has them |
| `VerifyProofShim/` | `zkcash::utils::fv_verify_proof_full_entry` | `verify_proof` together with the `Groth16Verifier` methods it drives. Already contained in `TransactShim`; kept as a separate, much smaller target because the curve assumptions are far easier to develop against it |
| `CheckPublicAmountShim/` | `zkcash::utils::fv_check_public_amount_entry` | `check_public_amount` alone, the smallest target — and the only one whose trusted base has real semantics rather than bare signatures |

The `fv_*` entry points are transcriptions of the real functions against a narrowed interface
(shim types instead of arkworks, plain `&mut` instead of Anchor's `AccountLoader`, `u64`
arithmetic instead of CPI transfers). They are marked extraction-only in the source, are never
called at runtime, and have to be kept in step with the real code by hand. `SETUP.md` lists them
and what each one replaces.

## The trusted base

Everything reachable from an entry point is mechanically extracted. Everything at the boundary
arrives in Lean as an assumption, in the hand-owned `*External.lean` files. `TransactShim` has 49
of them (44 functions, 5 types):

| Assumed | Count | Where |
|---|---|---|
| BN254 curve operations and the verifying key | 12 | `curve_shim.rs`: G1 deserialize / negate / serialize, `fr_lt_modulus_be`, the three `alt_bn128_*` syscalls, and the 5 verifying-key constants |
| Scalar-field (`Fr`) arithmetic | 8 | `fr_shim.rs` |
| Poseidon hashing | 6 | `light_hasher` |
| SHA-256 and `Hash::to_bytes` | 2 | `solana_sha256_hasher`, `solana_hash` |
| Borsh serialization | 5 | `u8`/`i64`/`u64`/`Vec`/`Pubkey` |
| Anchor error conversion | 3 | `anchor_lang::error` |
| Rust core/std plumbing | 8 | `TryFrom`, `checked_neg`, `Option::ok_or`, `Result::map_err`, `Display`/`ToString`, `io::Write` |
| Opaque types | 5 | `FrShim`, `G1Shim`, `Pubkey`, `Hash`, `std::io::Error` |

`VerifyProofShim` has 8 (the `curve_shim` subset). `CheckPublicAmountShim` has **none left**:
`FrShim` is defined as `ZMod bn254_r`, the BN254 scalar field, and its seven operations plus
`i64::checked_neg` are given real definitions in `CheckPublicAmountShim/FunsExternal.lean`.

`TransactShim/` and `VerifyProofShim/`'s `*External.lean` files are still the bare generated
templates — signatures with no content. Filling them is the main outstanding work, and
`extract.sh` deliberately never overwrites a hand-filled one.

## Why the shims are needed

Neither Charon nor Aeneas can consume arkworks' types. Charon crashes on `ark-ff`'s
const-generic `BigInt<N>` and its mutually recursive `Field`/`PrimeField` trait hierarchy;
Aeneas separately fails on `Field`'s GATs and on `num_bigint`'s `PartialEq for BigUint`. Marking
those crates `--opaque` does not help, because their types remain in the signatures of the code
being extracted, so Aeneas drops that code's bodies instead.

The technique that works is replacing the offending *types* at the Rust level: `FrShim`
(`fr_shim.rs`) for scalar-field elements and `G1Shim` plus the `alt_bn128_*` wrappers
(`curve_shim.rs`) for group operations — structurally trivial stand-ins exposing exactly the
operations the real code uses. Aeneas then sees something shaped like `Pubkey`, which already
extracts cleanly, and emits the shim operations as assumptions with real type signatures while
recovering all the surrounding control flow. Each shim lives in its own module so it can be
marked `--opaque` in one shot; Charon's name matcher does not reliably match individual methods
on a local struct. Both shim files document their own boundaries in detail.

## The spec, and what is proved

`lean/Spec/` holds the specification side, all of it work in progress:

- `written_spec.md` — the protocol written out in prose and mathematics.
- `privacy_cash_spec.lean` — a partial Lean translation of it: the field, the hash abstractions
  and their collision/preimage-resistance assumptions, keys, commitments, nullifiers, Merkle
  openings and zero hashes, the `RelationS` the circuit is meant to enforce, and Groth16
  verification.
- `theorems.lean` — the properties this is all aimed at (no double spending, no replay, value
  cannot be inflated, only deposited coins can be withdrawn, proof binding, and so on), so far
  as a list rather than statements.

The spec is derived from the protocol, not from the Rust — which is the point, since a spec read
off the code being checked proves nothing. The consequence is that **nothing currently connects
the spec to the extracted model**: `privacy_cash_spec.lean` does not import any of the three
generated libraries, and there are as yet no theorems relating them. Connecting the two is the
work this model exists to support.

## What is open

- **Nothing yet links the spec to the model.** The spec's `F`/`PubInputs`/`RelationS` and the
  model's `ZMod bn254_r`/byte arrays are separate universes; bridging them — starting from
  `check_public_amount`, whose trusted base already has real semantics — is the first step
  towards any of `theorems.lean`.
- **The `TransactShim`/`VerifyProofShim` assumptions have no content.** Until they do, the model
  states *that* an assumption exists, not what it computes. The consequential ones are the curve
  operations: on-chain those three `alt_bn128_*` calls are Solana syscalls executed by the
  validator, so nothing in this pipeline can derive them, and almost every guarantee `transact`
  provides is downstream of the proof check.
- **The abstraction itself needs review.** Reproducing the extraction cleanly shows the pipeline
  is stable, not that this is the right model to prove theorems against. Those are separate
  questions and only the first is settled.
- **`transact_spl` has not been attempted** with this technique.
- **`update_deposit_limit` and `update_global_config` do not extract.** The first crashes
  Charon on `AccountLoader::load_mut()` directly; the second crashes as a follow-on effect of
  the `--exclude` flag `extract.sh` needs for an `ErrorCode` naming collision. Neither blocks
  `transact`, which avoids `AccountLoader` entirely via plain `&mut` parameters.
- **One Aeneas codegen bug is patched by `sed` in `extract.sh`.** At the pinned revision the
  derived `PartialOrd::le` default method is emitted in a form the pinned Aeneas Lean library
  does not accept; binary and library are the same revision, so regenerating does not fix it.

## Sources

- [`AeneasVerif/charon#142`](https://github.com/AeneasVerif/charon/issues/142) — tracking issue
  for unsupported Rust features. Most items are resolved; it does not explain the `Fr` crash,
  which the shims sidestep rather than fix.
- [`AeneasVerif/aeneas` README](https://github.com/AeneasVerif/aeneas/blob/main/README.md) —
  "instantiating a generic type... with a mutable reference is not supported yet", the best
  current match for the `AccountLoader::load_mut()` crash.
