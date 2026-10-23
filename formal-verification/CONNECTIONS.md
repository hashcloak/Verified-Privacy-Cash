# Connection: code model ↔ spec

`lean/Connection/` connects the code model (`core-model/`: the extracted `zkcash_core` plus the
hand-written Solana/Anchor model) to the spec (`lean/Spec/`). Open work is in `TODO.md`; how
to review is in `REVIEWING.md`.

**Review surface** (four files; proofs in `Connection/Proofs/` are not for review):
- `ConnectionTheorems.lean`: the two connection theorems, the security goals stated of the code, and
  non-vacuity.
- `Findings.lean`: the differences found (L1, A0), as counterexamples and an exact statement.
- `Mapping.lean`: how code values map to spec values (`toF`, `toPubkey`, `toTree`, `toWorld`,
  `toInputs`), and code executions to spec runs (`runTxs`, `IsRunOf`, `IsSpecRun`).
- `Hypotheses.lean`: the hypotheses, each with its kind (below).

**Scope: safety.** Code accepts ⟹ spec allows, with the spec's effects. Wrong rejections show
up as findings where completeness is checked (`Findings.lean`: the handler); full completeness
through Anchor and the runtime, and with it G3a/G3b, is future work.

## Theorems (`ConnectionTheorems.lean`)

Kinds of hypothesis: **premise** (the situation the theorem is about), **asm** (approved
assumption), **design** (agreed by-design exclusion). No invariant is a hypothesis: `WellFormed`
is proved for every reachable state.

| Theorem | Says | Hypotheses (kind) |
|---|---|---|
| `transact_connection` | every `transact` the code accepts satisfies the spec's `transact` (all preconditions, exact effects) | execution, step (premise); program ≠ system program, `HashesAgree`, `SolanaFacts`, `CryptoFacts`, syscall contracts, `PairingLaws` (asm); `OutsideSpecDetail` (design) |
| `run_connection` | every execution is a run of the spec (`IsSpecRun`), or has not initialized the pool | execution (premise); program ≠ system program, `HashesAgree`, syscall contracts, `PairingLaws` (asm); `ExecutionAssumptions` (asm) |
| `spendsAreGenuine_code`, `noDoubleSpend_code`, `poolBacksNotes_code`, `onlyOwnerSpends_code`, `fullTreeFreezes_code`, `configOnlyByAuthority_code` | G1a, G1b, G1c, G1d, G3c, G5 (the spec's named properties) hold of the execution's run | as `run_connection`; initialized (premise) |
| `proofValid_code`, `copiedProofSamePayout_code`, `noSolCreated_code`, `exactPayouts_code` | G1e, G2a, G4a, G4b hold of every transaction the code accepts | as `transact_connection` |
| `connection_nonvacuous` | every hypothesis of `run_connection` and of the run goals holds in a toy execution (deposit, then a withdrawal spending its note), with witnesses where the spend is non-zero | none |
| `transact_connection_nonvacuous` | every hypothesis of `transact_connection` holds for an accepted deposit and an accepted withdrawal in one toy deployment | none |

Not carried over: G2b (about circuit witnesses only), G3a and G3b (liveness: need
completeness). All theorems are `sorry`-free and use only Lean's standard axioms.

## Findings

Details for the program's authors are in `FINDINGS.md`. No theorem excludes a finding.

| ID | What | Where in Lean |
|---|---|---|
| L1 | the code rejects `extAmt = 0`, the internal transfer the docs describe and the spec allows | `Findings.lean`: counterexamples; one of the two differences at the handler |
| A0 | the code rejects a proof whose `proof_a` is 64 zero bytes (arkworks rejects what the syscalls read as the identity) | `Findings.lean`: counterexample; the other difference at the handler |
| I1 | only the circuit keeps the two input nullifiers distinct | the assumption `CryptoFacts.distinctNullifiers` |
| F7 | a root can be evicted (about 50 transactions) before an honest proof lands | spec: `rootKnown` (a limit on G3a) |

Documentation notes (the spec includes the rule, marked NOT FROM THE DOCS): `extAmt = −2^63`
is rejected; the fee error margin is at most 10000; only the admin key can initialize.

## Outside the spec's level of detail (excluded by `OutsideSpecDetail`, by design)

The spec is written at the level of the documentation and deliberately leaves these out.
Only `transact_connection` (exact effects) excludes them; `run_connection` covers them as
changes the spec allows between transactions.

- **Pre-funded nullifier address:** Anchor only tops it up, so the signer pays less than
  `2 * nullifierRent`. Not a security issue (Anchor 0.31.1).
- **Payee is a nullifier account:** the payment is locked there; the spec doesn't count
  nullifier accounts.
- **Rent fixed:** the spec fixes the rent amounts; the code reads the `Rent` sysvar.


## Assumed, not derived

- `HashesAgree`: Poseidon, zero hashes, SHA-256 are the spec's; Poseidon outputs and the
  zero hashes are canonical.
- `CompletenessAssumptions` (`handler_complete_except_L1_A0` only): `HashesAgree`; the hashes
  and the `alt_bn128` syscalls return a value on valid input (`HashesSucceed`,
  `SyscallsSucceed`); the syscalls decode the program key's G2 points (`KeyG2Decodes`).
- `SolanaFacts`: rent positive; the transaction's data fits in a vector; the pool's address
  does not sign (a PDA has no key).
- `ExecutionAssumptions` (`run_connection`): every step's assumptions, as for
  `transact_connection`; the program's three fixed addresses differ (SHA-256).
- `CryptoFacts`: distinct nullifiers (circuit only; neither the program nor Anchor checks it,
  I1); the two new nullifier addresses differ (SHA-256).
- Verifier bridge: core-model's syscall contracts (`AltBn128Contracts`), and `PairingLaws`
  (the pairing is bilinear, and pairing with `-a` inverts). The spec's groups, pairing and key
  are instantiated from these and the program's key.
- Core-model's own assumptions (`core-model/README.md`), in particular `EnvStep`: nothing
  outside the program changes the owner or data of its accounts. Double-spend protection
  rests on it.
