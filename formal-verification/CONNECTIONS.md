# Connection: code model ↔ spec

`lean/Connection/` connects the code model (`core-model/`: the extracted `zkcash_core` plus the
hand-written Solana/Anchor model) to the spec (`lean/Spec/`). Open work is in `TODO.md`; how to review is in `REVIEWING.md`.

**Review surface** (three files; proofs in `Connection/Proofs/` are not for review):
- `Mapping.lean`: how code values map to spec values (`toF`, `toPubkey`, `toTree`, `toWorld`, `toInputs`).
- `Hypotheses.lean`: the main theorem's hypotheses: assumed (`HashesAgree`, `SolanaFacts`,
  `CryptoFacts`, `PairingLaws`), an invariant proved for every reachable state (`WellFormed`),
  and Solana details outside the spec's level of detail (`OutsideSpecDetail`).
- `Statements.lean`: the theorems, each a commuting square (SymCrypt style): run one code
  function, map inputs and result, compare with the spec.

**Scope: safety, plus exact per-function squares.** Code accepts ⟹ spec allows, with the
spec's effects. The per-function equations also catch wrong rejections (L1); elsewhere they
are not caught yet. Handler completeness is planned (`TODO.md`); full completeness, and with
it G3a/G3b, is future work.

## Theorems (`Statements.lean`)

Each hypothesis has a kind: **inv** (proved invariant), **asm** (approved assumption),
**design** (agreed by-design exclusion), or **OPEN** (not yet classified or proved). Premises
that set up the scenario ("the code accepted", "the tree is full") and the field links of the
external-data hash are not conditions and are not listed.

| Code | Spec | Hypotheses (kind) |
|---|---|---|
| `check_public_amount` | `pubAmtConsistent` ∧ `amountsInRange`: **FAILS** (L1); counterexample; L1 is the only difference | none |
| `is_known_root` | `rootKnown` (equal) | tree shape (inv); canonical history (OPEN: to prove, `TODO.md`); canonical root (OPEN: removed by the byte-level spec, `TODO.md`) |
| `is_known_root` (accepts ⟹ known) | `rootKnown` | tree shape (inv); canonical root (OPEN, as above; in `transact` discharged by `verify_proof`) |
| `validate_fee` | `feeSufficient` ∧ `amountsInRange` (iff) | rates ≤ 100% (inv) |
| `calculate_complete_ext_data_hash` | hashes exactly `serealizeExternalData`; `none` iff not `encOutsFit` | fits in a vector (asm, `SolanaFacts`) |
| `append` | `appendEffects` (if it returns) / `MerkleTreeFull` (no room) | `HashesAgree` (asm); tree shape (inv) |
| `verify_proof` | the 7 public inputs are canonical | none |
| `verify_proof` (verifier bridge) | `proofValid` (spec's `Groth16.verify`) | syscall contracts (asm, core-model); `PairingLaws` (asm) |
| `step … transact` (`transact_connection_verified`) | `transact` (all preconditions, exact effects) and `WellFormed` again | `WellFormed` (inv); `HashesAgree`, `SolanaFacts`, `CryptoFacts`, syscall contracts, `PairingLaws` (asm); `OutsideSpecDetail` (design) |
| any execution from genesis (`wellFormed_reachable`) | every reached state is `WellFormed` | program ≠ system program (asm) |
| **every `transact` in any execution** (`transact_connection_main`, MAIN RESULT) | `transact`, with the spec's nullifier set = nullifiers spent so far | as `transact_connection_verified`, without `WellFormed` (proved) |

`transact_connection` is the per-step result for any spec instances, with the bridge replaced
by a hypothesis `hProofValid`.

All are `sorry`-free and use only Lean's standard axioms.

## Findings

No code/spec difference is excluded at present. Findings for the program's authors are in
`FINDINGS.md`.

- **L1 (open, code rejects more):** `check_public_amount` rejects `extAmt = 0`, the internal
  transfer the docs describe and the spec allows. Lean proves the square false, with a
  counterexample. The composed `transact` theorem (safety) is unaffected.
- **`i64::MIN` (documentation note in `FINDINGS.md`):** the code rejects
  `extAmt = −2^63` (`checked_neg` overflows). Reasonable, but not in the docs; the spec's
  `amountsInRange` now excludes it (marked NOT FROM THE DOCS).

- **F1 (resolved, spec bug):** the spec checked the pool before a deposit's fee,
  the code after. The code is right (the deposit exceeds the fee); `poolSolvent` now checks
  after the deposit, and the hypothesis is gone.
- **F3 (resolved, spec too strict):** `poolIsSeparate` forbade the pool as a payee
  even where nothing is paid to it. It now forbids only paying the pool from itself, which
  the runtime's lamport check rules out; the connection proves this from that check.

## Outside the spec's level of detail (excluded by `OutsideSpecDetail`, by design)

The spec is written at the level of the documentation and deliberately leaves these out.

- **Pre-funded nullifier address** (was F2): Anchor only tops it up, so the signer pays less
  than `2 * nullifierRent`. Not a security issue (Anchor 0.31.1).
- **Payee is a nullifier account** (was F4): the payment is locked there; the spec doesn't
  count nullifier accounts.
- **Rent fixed:** the spec fixes the rent amounts; the code reads the `Rent` sysvar.


## Assumed, not derived

- `HashesAgree`: Poseidon, zero hashes, SHA-256 are the spec's.
- `SolanaFacts`: rent positive; the transaction's data fits in a vector.
- `CryptoFacts`: distinct nullifiers (circuit only; neither the program nor Anchor checks it,
  finding I1); the two new nullifier addresses differ (SHA-256).
- Verifier bridge: core-model's syscall contracts (`AltBn128Contracts`), and `PairingLaws`
  (the pairing is bilinear, and pairing with `-a` inverts). The spec's groups, pairing and key
  are instantiated from these and the program's key.
- `WellFormed` is not assumed in the main result: proved for every reachable state.
