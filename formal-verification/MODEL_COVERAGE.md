# Model coverage checklist

What is modelled, what is not, and what gates the rest. Companion to `MODEL_REPORT.md`
(which describes the pipeline); this file tracks *how much is left*.

Line counts are from `anchor/programs/zkcash/src/lib.rs`.

---

## 0. Prerequisites

These gate everything below. Doing them after the per-instruction work costs
significantly more.

- [ ] **Seam refactor.** Split each handler into `unpack accounts -> core(plain data,
      &mut state) -> apply effects`. The cut point already exists: the
      `let tree_account = &mut ctx.accounts.tree_account.load_mut()?;` line at lib.rs
      110 / 199 / 218 / 376.
      Kills the `AccountLoader::load_mut()` blocker for all four instructions at once,
      and removes the need to hand-write six more `fv_*` twins.
      *Est. 1-2 days for the pattern + transact, then ~0.5 day per instruction.*

- [x] **Shared trusted base (`Common/`).** DONE. `bn254_r`, `fr_shim.FrShim` and the
      whole BN254 curve surface (`G1Shim` + 6 ops + `fr_lt_modulus_be`) now live in
      `lean/Common/{Bn254,FrShim,Curve}.lean` instead of once per model. The FrShim
      bodies were byte-identical across models; `curve_shim.G1Shim` was worse -- a
      separate `axiom : Type` per model, so genuinely different types that no proof
      could transfer between. `lake build` passes; `Test/CommonBase.lean` guards it.
      Net -84 lines. `Common/` is hand-owned and `extract.sh` never touches it.

- [ ] **Single-root extraction.** Confirm `charon rustc --start-from` is repeatable:
      `nix develop path:. -c charon rustc --help | grep -A3 start-from`
      - [ ] repeatable -> pass all roots in one run (one-line change to `extract.sh`)
      - [ ] not repeatable -> write one Rust fn calling all cores, `--start-from` that
      **Confirmed necessary, with a concrete failure.** `Common/` fixed the hand-owned
      half of the duplication, but the GENERATED half still collides. Importing two
      models fails:

          environment already contains
          'zkcash.utils.fv_verify_proof_full_entry_loop0_loop3.body.eq_1'
          from TransactShim.Funs

      `fv_transact_entry` calls `fv_verify_proof_full_entry` and
      `fv_check_public_amount_entry`, so TransactShim's closure already CONTAINS both
      smaller models, and aeneas emits those functions again into each library.
      `Common/` cannot deduplicate what aeneas regenerates.

      Consequence: **VerifyProofShim and CheckPublicAmountShim are strict subsets of
      TransactShim** -- development scaffolding, not components. Whole-contract theorems
      need to span instructions, so the union must be one library.
      *Est. 1 hour if repeatable, half a day for the fallback.*

- [ ] **Retire the `fv_*` twins.** `fv_transact_entry` (lib.rs:549) is a ~150-line hand
      transcription of `transact`, never called at runtime, with no test comparing them.
      Its correspondence to the real code is the single largest assumption in the
      project and appears on no trusted-base list. The seam refactor removes it.

---

## 1. Instructions (7 total, 1 modelled)

| # | instruction | lib.rs | lines | status | blocker |
|---|---|---|---|---|---|
| 1 | `transact` | 217 | ~158 | modelled via hand twin | twin drift (see 0) |
| 2 | `transact_spl` | 375 | ~150 | not attempted | SPL CPI + `load_mut` |
| 3 | `initialize` | 72 | ~37 | not attempted | none known |
| 4 | `initialize_tree_account_for_spl_token` | 155 | ~40 | not attempted | none known |
| 5 | `update_global_config` | 121 | ~34 | crashes Charon | `--exclude` follow-on |
| 6 | `update_deposit_limit_for_spl_token` | 195 | ~22 | not attempted | `load_mut` |
| 7 | `update_deposit_limit` | 109 | ~12 | crashes Charon | `load_mut` |

Recommended order (not size order):

- [ ] **`transact`** — re-extract through the refactored seam, drop the twin
- [ ] **`initialize`** — small, but establishes the *initial state*. Without it, every
      theorem is a claim about an arbitrary starting tree rather than a real one.
      Higher value than its 37 lines suggest.
- [ ] **`update_deposit_limit`** — 12 lines; first test that the seam refactor cleared
      the `load_mut` blocker
- [ ] **`update_global_config`** — separate blocker: rename the colliding `ErrorCode`
      variant or narrow the `--exclude`. *Possibly 1 hour.*
- [ ] **`initialize_tree_account_for_spl_token`**
- [ ] **`update_deposit_limit_for_spl_token`**
- [ ] **`transact_spl`** — last; brings a new trusted surface (below)

*Est. 3-5 days for all six once prerequisites are done.*

### New trusted surface from SPL

- [ ] `token::transfer` CPI (3 call sites in `transact_spl`)
- [ ] `TokenAccount`, `Mint` types
- [ ] token-account / mint-address validation checks (these are **logic**, in the model —
      not effects)

*Est. 2-3 days.*

---

## 2. Trusted base: 22 -> 6

Current: 22 DERIVED / 22 TRUSTED in `lean/TransactShim/FunsExternal.lean`.
Target: only the assumptions that genuinely cannot be discharged.

### DIAGNOSTIC — 5 axioms -> 0

- [ ] Prove the claim the comments already assert: these values never reach state
      (reached only on error paths, before any account is written)
- [ ] Then define all five as total junk; the theorem is what licenses it
- [ ] Decide consciously: junk definitions mean you can prove state-transition
      theorems but not "fails with error code X"

### CRYPTO — 6 axioms -> 3

- [ ] `ID` -> `def`. It is `const ID: u8 = 0` (light-hasher `poseidon.rs:81`)
- [ ] `zero_bytes` -> define as the ladder `Z(k+1) = hashv [Z k, Z k]`, **not** as 41
      transcribed constants. Currently nothing connects those constants to Poseidon at
      all, so the model cannot know the zero-subtree ladder uses the same hash as real
      nodes. This is a real gap, not bookkeeping.
- [ ] `zero_indexed_leaf` -> transcribe (base of the ladder)
- [ ] **Keep abstract, permanently:** `hash`, `hashv`, `solana_sha256_hasher::hash`.
      Two reasons: on-chain they are the `sol_poseidon` / `sol_sha256` syscalls; and
      collision resistance is *false* of any concrete 32-byte-output function, so it
      can only be stated about an abstract one. Defining them would make the model
      strictly less useful.

### CURVE — 11 axioms -> 3

- [ ] 5 verifying-key constants -> transcribe from `utils.rs:17-62`. Opaque only
      because `curve_shim` is `--opaque`; no trust is involved.
      - [ ] Add a drift guard (test pinning the values). The Rust side const-evals from
            `VERIFYING_KEY` so it "cannot drift"; a Lean transcription has no such link.
- [ ] `deserialize_uncompressed`, `negate`, `to_bytes` -> define via Mathlib's
      `WeierstrassCurve.Affine.Point` over `ZMod q`, `y^2 = x^3 + 3`.
      These are **not** syscalls — they are arkworks code compiled into the BPF program.
      BN254 G1 has cofactor 1, so on-curve already implies prime-order subgroup.
      *Est. 1-2 weeks; Mathlib's affine group law is real but heavy.*
- [ ] **Keep as assumptions:** `alt_bn128_addition`, `alt_bn128_multiplication`,
      `alt_bn128_pairing`. Genuine syscalls. State them *against* Mathlib's group law
      (add/mul) and the abstract `Pairing` class (pairing) — with content, not as bare
      signatures.

### Types — 2 axioms -> 0

- [ ] `curve_shim.G1Shim` -> Mathlib point type
- [ ] `std.io.error.Error` -> `Unit` (never inspected; no constructor needed)

### Endgame

6 assumptions, of two kinds:

- **3 hash functions** — cryptographic assumptions, correct to keep
- **3 curve syscalls** — facts about the validator, unavoidable

That is exactly the assumption list a cryptographer would write for a Groth16-based
shielded pool. Everything else is dischargeable engineering.

---

## 3. First proof

- [ ] **Prove one property end to end**, spec -> model. `check_public_amount` is the
      candidate: it is the only shim with zero axioms remaining, so nothing blocks it.

Until one such proof exists, the pipeline is known to reproduce but the model is not
known to be the right one. `MODEL_REPORT.md` says this already:

> "Reproducing the extraction cleanly shows the pipeline is stable, not that this is
> the right model to prove theorems against."

**Do this before scaling coverage.** Seven modelled instructions with zero theorems is
seven times more unproven model.

---

## Rough totals

| bucket | estimate |
|---|---|
| prerequisites (section 0) | 2-3 days |
| remaining 6 instructions | 3-5 days |
| SPL trusted surface | 2-3 days |
| trusted base 22 -> 6 | 1-2 weeks |
| first proof | unknown — it is the experiment |

Coverage alone: ~2 weeks. Coverage plus a trusted base worth trusting: ~4-5 weeks.
