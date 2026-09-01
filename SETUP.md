# Setup

Two separate environments, for two separate purposes — covered here as two parts of one doc so
there's a single place to look, not because they're the same thing:

- **Part 1** builds and tests the real `zkcash` program (`anchor/`).
- **Part 2** runs the Charon/Aeneas toolchain that extracts a Lean model of it
  (`formal-verification/`) — a separate `flake.nix`, kept apart from Part 1's dev shell
  deliberately, since it's for verifying the program, not building/deploying it.

## Part 1: Building and testing `zkcash`

1. Enter the dev shell (from repo root, every session):
   ```bash
   nix develop path:.
   ```
2. Install JS deps:
   ```bash
   cd anchor
   npm install
   ```
3. Create a local wallet (only if `deploy-keypair.json` doesn't exist yet):
   ```bash
   solana-keygen new -o deploy-keypair.json
   ```
4. Build:
   ```bash
   anchor build -- --features localnet
   ```
5. If the build/tests fail with `DeclaredProgramIdMismatch`, run:
   ```bash
   anchor keys sync
   ```
   then open `Anchor.toml` and make sure `[programs.devnet]` and `[programs.localnet]` show the
   same pubkey as `[programs.mainnet]` and the updated `lib.rs`. Fix any that don't match by hand.
   Then rebuild:
   ```bash
   anchor build -- --features localnet
   ```

### Running tests

```bash
npm run test:sol           # SOL deposit/withdraw flow
npm run test:spl           # SPL token flow
npm run test:mint-checked  # SPL mint-checked variant
cargo test                 # Rust unit tests
```

`test:sol` takes about 2 minutes. If it runs much longer than that with no new output, `anchor
test` has hung on shutdown after finishing — kill it:
```bash
pkill -f solana-test-validator; pkill -f ts-mocha
```

**What "normal" looks like:**
- `test:sol`: usually ~29-30 passing, 0-1 flaky failure (`Blockhash not found` — a stale-blockhash
  race, just re-run if it bothers you).
- `test:spl`: currently fails wholesale (0 passing), mostly with `VersionedTransaction too large:
  ... (max: encoded/raw 1644/1232)`. That 1232-byte limit is a Solana protocol constant, not a
  validator or nix setting — this is a pre-existing issue in the repo/tests, not something to debug
  via the dev environment.

## Part 2: Formal-verification toolchain (Charon + Aeneas)

**Charon** converts a Rust crate into an intermediate format; **Aeneas** turns that into Lean 4
code mirroring the original Rust. The goal is a Lean model of `zkcash`, together with a clear
account of what that model asserts versus what it mechanically derives (the "trusted base").

### Reproducing the model

Setup (once), from `formal-verification/` inside `nix develop path:.`:
```bash
./setup-vendor.sh                                          # vendors + strips cdylib from 17 deps
cp cargo-config.toml.template ../anchor/.cargo/config.toml  # wires the patch in
```

Then produce the model:
```bash
./extract.sh
```
This regenerates `lean/TransactShim/`, `lean/VerifyProofShim/` and
`lean/CheckPublicAmountShim/` — the Lean model of `transact` (SOL-only for now) — and builds it.
Tested to reproduce `MODEL_REPORT.md`'s results from a completely clean
`vendor`/`lean`/`.llbc` state. `extract.sh`'s own comments explain the one
non-obvious step (why it needs `charon`'s own build output, not a plain `cargo build`) — read those
before changing it.

**Trusted base** (what's asserted, not derived): BN254 scalar-field arithmetic, the BN254 group
operations Groth16 verification is built from, Poseidon and SHA-256 hashing, and Anchor's
`AccountLoader`/CPI mechanics. Everything else in the model is real, mechanically-extracted
control flow. `MODEL_REPORT.md`'s "The trusted base" itemises all of it.

### Why the extra setup is needed

Reproduced on **macOS (Apple Silicon)** and **Linux (Manjaro)**. Both problems below are the same
root cause hitting two different places:

1. **17 of `zkcash`'s dependencies build an unused Solana program artifact.** Solana on-chain
   programs are built as a `cdylib` (a dynamic library the Solana runtime can load). Following that
   convention, 17 dependencies (`solana-program`, `solana-zk-sdk`, every `spl-*` crate) declare
   themselves buildable as a `cdylib`, even though here they're only ever used as ordinary Rust
   libraries — nothing links against that output. Cargo is smart enough to skip building it; Charon
   isn't, and that specific build step fails to link on both macOS and Linux. On Linux, `charon
   cargo` dies compiling `solana-nostd-keccak`'s cdylib with a rust-lld `duplicate symbol:
   core::panicking::*` error (`sha3` vs `keccak`), before it ever reaches `zkcash`.
   `setup-vendor.sh` fixes this by
   vendoring those 17 crates and stripping the unused `cdylib` declaration from each — harmless to
   run even if a given machine doesn't hit the failure.
2. **`zkcash` itself declares `cdylib` too — correctly**, since it needs it for real deployment, so
   this one wasn't edited. Charon still tries to build that unused output and hits the same linking
   problem. `extract.sh` avoids it a different way: `charon rustc` (explicit compiler flags) instead
   of `charon cargo` (which reads `Cargo.toml` and infers the build type), forcing the build type to
   a plain library instead.

### Linux notes

Everything above applies on Linux as well as macOS. Three further issues showed up on Manjaro and
are worth knowing about before blaming the pipeline:

1. **`nix develop path:.` can SIGSEGV on shell entry**, while crashing in the nix-shell-env build
   rather than in anything this project owns — the toolchain itself builds fine. Sidestep the
   interactive shell entirely:
   ```bash
   nix print-dev-env path:. > devenv.sh
   source devenv.sh
   ```
2. **A system `LD_LIBRARY_PATH` SIGSEGVs the nix-built `charon` and `aeneas` binaries**, including
   trivial invocations. If the environment sets something like `LD_LIBRARY_PATH=/usr/lib64:`,
   `unset LD_LIBRARY_PATH` before running the extraction.
3. **Lean's bundled `clang` picks up the system `libclang-cpp` and aborts** whenever lake compiles
   native code (Mathlib's `cache` executable, any `lean_exe`), failing on an undefined
   `llvm::sys::fs::getMainExecutable` symbol. The fix is to put Lean's own lib directory first:
   ```bash
   export LD_LIBRARY_PATH="$(lean --print-prefix)/lib:$LD_LIBRARY_PATH"
   ```
   `extract.sh` already does this for its own Lean build step, layering it on top of the cleared
   value from (2). Pure `.olean` elaboration — typechecking, editing via the LSP — never invokes
   clang, so interactive work in the model doesn't need it; only native compilation does.

Two CLI quirks that look like breakage but aren't: `charon` has no `--version` (it only takes
subcommands), and `aeneas` spells it `-version` with a single dash.

### Source changes made to enable this

Additive only — no existing program logic changed. All of it is marked in-source as
extraction-only and should be reviewed (and possibly gated or removed once the model is complete)
before any of it goes near production.

| File | What was added | Why |
|---|---|---|
| `anchor/programs/zkcash/src/fr_shim.rs` (new) | `FrShim`, a `[u8; 32]`-wrapping stand-in for `ark-bn254::Fr`, no real implementation | Real `Fr` crashes Charon; its own module lets it be marked `--opaque` reliably |
| `anchor/programs/zkcash/src/curve_shim.rs` (new) | `G1Shim`, the `alt_bn128_*` wrappers, `fr_lt_modulus_be`, and the verifying key as plain arrays | Same, for the arkworks/`num-bigint` types `verify_proof` uses |
| `anchor/programs/zkcash/src/utils.rs` | `fv_check_public_amount_entry`, plus `fv_verify_proof_full_entry` and `fv_change_endianness_64` — transcriptions of `check_public_amount` and of `verify_proof` + the `Groth16Verifier` methods it drives, against the shims | Lets Aeneas extract their real control flow |
| `anchor/programs/zkcash/src/lib.rs` | `fv_transact_entry`, a transcription of `transact` against plain `&mut` params | Lets Aeneas extract `transact`'s real control flow end to end |
| `anchor/.cargo/config.toml` (gitignored, from the template above) | `[patch.crates-io]` entries for the 17 vendored/patched dependencies | Wires problem #1's fix in |

`formal-verification/` holds the toolchain and generated Lean output
(`lean/TransactShim/`, `lean/VerifyProofShim/`, `lean/CheckPublicAmountShim/`).

### Two smaller reference notes

- **Targeting a method directly** isn't something the current model needs (`fv_transact_entry` is
  a plain function; the `MerkleTree` methods it calls are resolved fine as ordinary calls inside an
  already-targeted function). If a future target ever needs `--start-from` a method itself, Charon
  can silently return an empty result — the fix is a one-line free-function wrapper next to it. Not
  currently blocking anything; recorded so it doesn't need rediscovering.
- **Naming:** the crate is `zkcash`, and Anchor's `#[program]` macro wraps instructions in a module
  also named `zkcash`, so a real instruction is `zkcash::zkcash::transact_spl`, not
  `zkcash::transact_spl`. `fv_transact_entry` avoids this by living outside that module.

### Status and caveats

This is work in progress. Reproducing the extraction cleanly shows the pipeline is stable; it does
not show that this is the right model to prove theorems against. The extraction flow and the
trusted base both still need a critical review rather than a confirming one — `MODEL_REPORT.md`'s
"What is open" lists the specific gaps, the largest being that the assumptions in
`TransactShim/` and `VerifyProofShim/`'s `*External.lean` files are still bare signatures with
no content.
