# Lean model of `zkcash`: results

The Lean 4 model generated for `zkcash` (`anchor/programs/zkcash`) via Charon + Aeneas. Environment
setup and how to reproduce this are in `SETUP.md`. This covers what was extracted, how, and what's
still open.

## Bottom line

`transact` — the core deposit/withdrawal instruction — extracts and translates completely: 12/12
real functions transparent, 71/71 trusted primitives opaque, zero errors, zero `sorry`/`admit`/
`fail panic` anywhere in the output. The Lean output (`lean/TransactShim/`) is one self-contained
model of the real instruction — root check, ext-data-hash check, `check_public_amount`,
`validate_fee`, proof verification, both balance-update branches, the fee transfer, and both
`MerkleTree::append` calls — composed in the order the real source has them, confirmed directly
against the generated files, not just tool exit codes.

Charon can't translate code touching `ark-bn254`'s `Fr` type (crashes on `ark-ff`'s const-generic
`BigInt<N>`/mutually-recursive trait hierarchy). The fix is a **shim type** (`FrShim`, `fr_shim.rs`):
a trivial `[u8; 32]`-wrapping stand-in exposing the same operations, so Aeneas sees something
shaped like the already-working `Pubkey` type instead of `ark-ff`'s real hierarchy — recovering
`transact`'s real control flow without ever translating the arithmetic itself. Combined with plain
`&mut` parameters standing in for Anchor's `AccountLoader`/CPI mechanics, and one `--exclude` flag
for an `ErrorCode` naming collision, all extraction blockers are resolved for `transact`.

## What extracted

| Function | Result |
|---|---|
| `utils::validate_fee`, `utils::calculate_complete_ext_data_hash` | Clean |
| `merkle_tree::MerkleTree::is_known_root` / `initialize` / `append` | Clean (via wrapper functions) |
| `utils::check_public_amount` (via `FrShim`) | Clean — 1 real function transparent, 10 opaque axioms |
| `zkcash::transact` (via the full wrapper) | Clean — 12 real functions transparent, 71 opaque axioms |
| `zkcash::update_deposit_limit` | Crashes on `AccountLoader::load_mut()` directly (not needed for `transact` — worked around there via plain `&mut` params) |
| `zkcash::update_global_config` | The `ErrorCode` collision workaround causes a follow-on crash here specifically (not observed on `transact`) |

## The technique

Three trust boundaries Aeneas can't cross, each abstracted at the Rust level before extraction:

1. **`Fr` field arithmetic** — `FrShim` in `fr_shim.rs`. Needs to live in its own module (not
   inline with real logic) because Charon's `--opaque` name-matcher doesn't reliably resolve
   individual methods on a local struct (confirmed across 6+ pattern variants — none matched), but
   marking the *whole module* opaque (`--opaque "zkcash::fr_shim"`) works reliably. That's what
   makes Aeneas emit `FrShim`'s operations as proper `axiom`s with real type signatures, instead of
   inlining their placeholder bodies as `fail panic`.
2. **Proof verification** — `fv_verify_proof_entry`, a placeholder for `verify_proof`. Its Groth16
   pairing arithmetic isn't extracted, same reason as `Fr` — but the function itself is one of the
   most consequential parts of the whole model: `transact`'s correctness depends entirely on what a
   `true` result is assumed to guarantee.
3. **`AccountLoader`/CPI mechanics** — the wrapper takes plain `&mut MerkleTreeAccount`/`&mut u64`
   instead of `AccountLoader`/`AccountInfo`. Anchor's account resolution is already a trusted
   precondition, not something this project derives.

`fv_transact_entry` in `lib.rs` is a line-for-line transcription of `transact`'s real body against
this narrowed interface — a single `--start-from` run that pulls in `check_public_amount`,
`validate_fee`, `is_known_root`, and `append` as real sub-calls in one coherent output, not
disconnected files.

## What's open

- **The trusted base needs review, not just listing.** The three items above pin down *that* an
  axiom exists (e.g. `axiom FrShim.from_u64 : U64 → Result FrShim`) but not what it computes. Real
  semantic content — especially for `fv_verify_proof_entry`, since almost every guarantee `transact`
  provides is downstream of it — needs an independently-sourced spec to write against, which
  doesn't exist yet (an earlier draft was produced by reading this same code, defeating the point
  of a spec, and was deleted rather than left around to be mistaken for progress).
- **The whole extraction flow needs review, not just the result.** Reproducing cleanly proves the
  pipeline is stable, not that this is the right model to build theorems against. Reproducibility
  and correctness of the abstraction are separate questions; only the first one is settled.
- **`update_deposit_limit`/`update_global_config` crashes** are real but don't block `transact` —
  worth confirming they don't resurface if `transact_spl` is attempted.
- **`transact_spl`** hasn't been attempted with this technique yet.

## Sources

- [`AeneasVerif/charon#142`](https://github.com/AeneasVerif/charon/issues/142) — tracking issue for
  unsupported Rust features. Most items are checked off/resolved; not the explanation for the `Fr`
  crash — the shim sidesteps it rather than resolving its root cause.
- [`AeneasVerif/aeneas` README](https://github.com/AeneasVerif/aeneas/blob/main/README.md) — states
  "instantiating a generic type... with a mutable reference is not supported yet." Best current
  match for the `AccountLoader::load_mut()` crash.
