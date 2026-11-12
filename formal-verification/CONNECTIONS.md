# Connection: code model ↔ spec

`lean/Connection/` connects the code model (`core-model/`: the extracted `zkcash_core` plus the
hand-written Solana/Anchor model) to the spec (`lean/Spec/`). Open work is in `TODO.md`; how
to review is in `REVIEWING.md`.

## Theorems (`ConnectionTheorems.lean`; the `…_code` goals and their non-vacuity in `CodeModelStatements.lean`)

Kinds of hypothesis: **premise** (the situation the theorem is about), **asm** (approved
assumption), **design** (agreed by-design exclusion), **owner** (the honest owner's choice),
**limit** (what can legitimately block a spend), **finding** (a difference excluded by name). No
invariant is a hypothesis: `WellFormed` is proved for every reachable state.

| Theorem | Says | Hypotheses (kind) |
|---|---|---|
| `transact_connection` | every `transact` the code accepts satisfies the spec's `transact` (all preconditions, exact effects) | execution, then the transaction as one more step (core-model `Run`) (premise); `DeploymentFacts`, `HashesAgree`, `SolanaFacts`, `CryptoFacts`, syscall contracts, `PairingLaws` (asm); `OutsideSpecDetail` (design) |
| `run_connection` | every execution is a run of the spec (`IsSpecRun`), or has not initialized the pool | execution (premise); `DeploymentFacts`, `HashesAgree`, syscall contracts, `PairingLaws` (asm); `ExecutionAssumptions` (asm); `ExecutionOutsideSpecDetail`: rent fixed (design) |
| `execution_path_iff_run` | `ExecutionPath` (which `run_connection` takes) has exactly the executions of core-model's `Run` | none |
| `handler_complete_except_L1_A0` | completeness at the handler: every transaction the spec allows, the handler accepts with the spec's effects | `HandlerContext`, `HandlerSpecAllows` (premise); `CompletenessAssumptions`, syscall contracts, `PairingLaws` (asm); not L1, not A0 (finding) |
| `spendsAreGenuine_code`, `noDoubleSpend_code`, `poolBacksNotes_code`, `onlyOwnerSpends_code`, `onlyAuthoritiesChangeConfig_code`, `adminPowersLimited_code` | G1a, G1b, G1c, G1d, G5a, G5b (the spec's named properties) hold of the execution's run | as `run_connection`; initialized (premise) |
| `samePayout_code`, `onlySignersPay_code`, `exactPayouts_code` | G2a, G4a, G4b hold of every transaction the code accepts | as `transact_connection` |
| `honestSpendIsAccepted_code` | G3a: an honest spend is accepted by `step`, or a hash break occurs | execution (premise); `DeploymentFacts`, `CompletenessAssumptions`, syscall contracts, `PairingLaws`, `r.WitnessesFor wit` (T1) (asm); world = `r.final` (design); `ReachesProgram` (see below); not L1, not A0 (finding); `HonestSpend` (owner); `LimitsNotHit` (limit) |
| `adminsCannotLockWithdrawals_code` | G3b: a way to withdraw `spentAmt` ≥ 2 exists, at least half reaches the recipient, and an honest transaction using it is accepted by `step`, or a hash break occurs | as G3a, but L1 can't arise; `spentAmt` (premise); `LimitsNotHit` minus the fee and deposit limit (limit) |
| `admin_change_nonvacuous` | every hypothesis of `run_connection` holds in a toy execution with `update_deposit_limit` before a deposit, and every run of it records that admin change (G5a, G5b not vacuous on an admin change) | none |
| `liveness_code_nonvacuous` | every hypothesis of G3a and G3b for the code holds for a toy withdrawal of a 2-lamport note, for every split G3b allows (1/1 and 2/0), and `step` accepts it | `usize` is 64 bits (asm: unprovable in Lean) |
| `connection_nonvacuous` | every hypothesis of `run_connection` and of the run goals holds in a toy execution (deposit, then a withdrawal spending its note), with witnesses where the spend is non-zero | none |
| `donation_nonvacuous` | every hypothesis of `run_connection` holds in a toy execution with an outside action (`EnvStep`: 1 lamport sent to the pool) before a deposit, and every run of it has `r.donated = 1` | none |
| `handler_complete_nonvacuous` | every hypothesis of `handler_complete_except_L1_A0` holds for a toy deposit of 1 lamport with a nonzero `proof_a` | `usize` is 64 bits (asm: unprovable in Lean) |
| `transact_connection_nonvacuous` | every hypothesis of `transact_connection` (so of G2a, G4a, G4b for the code) holds for an accepted deposit and an accepted withdrawal in one toy deployment | none |

`ReachesProgram`: `AccountsCorrect` (owner); `ProgramAccountsInPlace`, `NullifierAddressesFree`,
`SolanaFacts`, positive rent (`TxEnv.RentPositive`, as core-model's `Run`) (asm); rent fixed (design); `SignerCreditFits` (limit).

Not carried over: G2b (about circuit witnesses only). The build has no `sorry`. Axioms are machine-checked for the spec only (`Spec/Axioms.lean`); for the connection, check with `#print axioms` (`REVIEWING.md`).

## Findings

Details for the program's authors are in `FINDINGS.md`. Only the completeness theorems (`handler_complete_except_L1_A0`, G3 for the code) exclude findings, by name.

| ID | What | Where in Lean |
|---|---|---|
| L1 | the code rejects `extAmt = 0`, the internal transfer the docs describe and the spec allows | `Findings.lean`: counterexamples (given a 64-bit `usize`); excluded in `handler_complete_except_L1_A0` |
| A0 | the code rejects a proof whose `proof_a` is 64 zero bytes (arkworks rejects what the syscalls read as the identity) | `Findings.lean`: counterexample (given a 64-bit `usize`); excluded in `handler_complete_except_L1_A0` |
| I1 | only the circuit keeps the two input nullifiers distinct | the assumption `CryptoFacts.distinctNullifiers`; without it `transact_connection` fails (`Proofs/ToyDup.lean`: `transact_connection_fails_without_distinct`) |
| F7 | a root can be evicted (about 50 transactions) before an honest proof lands | spec: `rootKnown` (a limit on G3a) |

Documentation notes (the spec includes the rule, marked ADDED MANUALLY (docs silent)):
`extAmt = −2^63` is rejected; the fee rates and the fee error margin are at most 10000; only the admin key can initialize.

## Assumed, not derived

What each says is in its docstring. Linking the code to the spec (`Hypotheses.lean`):

- `HashesAgree`: the deployment's hashes are the spec's.
- By design: `OutsideSpecDetail`, `ExecutionOutsideSpecDetail` (Solana details the spec does not model).

About the code alone (`CodeModelAssumptions.lean`; core-model does not state them):

- `DeploymentFacts`: the program is not the System Program, so an account the program owns is never mistaken for a free one.
- `SolanaFacts`: no program-derived address signs, per transaction. (Positive rent is part of core-model's `Run`.)
- `CryptoFacts`: circuit and SHA-256 facts, per transaction (includes I1).
- `ExecutionAssumptions` (`run_connection`): `SolanaFacts` and `CryptoFacts` for every `transact`; the fixed addresses differ.
- `CompletenessAssumptions` (`handler_complete_except_L1_A0`, G3a, G3b; in `Hypotheses.lean`, as it includes `HashesAgree`): the hashes and syscalls return a value on valid input; `usize` is 64 bits (SOLANA FACT, unprovable in Lean).
- `ProgramAccountsInPlace`, `NullifierAddressesFree` (in `ReachesProgram`, G3 for the code): Anchor's account constraints hold.
- Syscall contracts (`AltBn128Contracts`) and `PairingLaws`: the verifier bridge.
- Core-model's own assumptions (`core-model/README.md`), in particular `EnvStep`, on which double-spend protection rests.
