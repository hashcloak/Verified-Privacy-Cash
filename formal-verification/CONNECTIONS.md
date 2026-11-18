# Connection: where it stands

`lean/Connection/` proves that the code model (`core-model/`) behaves as the spec
(`lean/Spec/`) says. This page answers three questions: what is proved, what you must trust for
it to mean something, and what differences were found. How to review: `REVIEWING.md`.

## What is proved

- **The code accepts nothing the spec forbids.** Every `transact` the code accepts satisfies
  the spec's `transact`: every precondition, exactly the spec's effects. Every execution from
  genesis (transactions, admin instructions, outside actions such as donations) is a spec run.
  No difference found.
- **The code accepts everything the spec allows, except L1 and A0.** Whatever `transact` the
  spec allows, the code's `step` accepts, Anchor's account checks included. Every spec run is
  the run of some code execution. The two exceptions are findings (below).
- **So the spec's security goals hold of the code:** G1 (balance), G2a (non-malleability), G4
  (payouts), G5 (admin control); G3a and G3b (liveness) except L1 and A0. G2b has no code
  version: it is about circuit witnesses only.

Every result ends in "… or an address collision occurs" (a SHA-256 collision between two
derived addresses), as the spec's results end in a hash break. Collisions are not assumed away.

Not covered: Solana rejections that core-model leaves out (writable flags, rent exemption,
compute and size limits; `core-model/README.md`), so "accepted" means accepted by core-model's
`step`. For G3: a transfer or admin change after the run's last transaction.

## What you must trust

The spec's own assumptions T0–T3 (`Spec/Statements.lean`), core-model's
(`core-model/README.md`), and these. **S** = soundness needs it, **C** = only completeness and
G3 need it.

| Assumption | Says | Why it holds | |
|---|---|---|---|
| `ProgramNotSystem` | the program is not the System Program | nothing can be deployed at that address | S |
| `HashesAgree` | the spec's `H2` and `sha256` are the program's Poseidon (on canonical inputs) and SHA-256 | the spec leaves them abstract; this picks the real ones | S |
| `SameRent` | the transaction sees the rent the spec uses | the spec has one rent constant (by design) | S |
| syscall contracts, `PairingLaws` | what the `alt_bn128` syscalls return means; `e(−a, b) = e(a, b)⁻¹` | core-model's contracts; bilinearity | S |
| `PdasDoNotSign` | no derived address signs a transaction | a derived address has no private key | S |
| `CircuitFacts` | an accepted proof's two input nullifiers differ | only the circuit checks this (finding I1) | S |
| `CryptoSucceeds` | Poseidon and the syscalls return a value on valid input; the key's G2 points decode | `light-poseidon` and Solana's syscalls fail only on invalid input | C |
| `RuntimeFacts` | `usize` is 64 bits; rent is positive | the program runs on 64-bit SBF; Solana charges for account metadata | C |
| `PdasOnlyByProgram` | only the program creates accounts at its derived addresses | creating one needs the address's signature | C |
| `SignerIsPlain` (by design) | the signer is a system account with no data | the spec does not model owners; on Solana only such an account pays | C |

Double-spend protection also rests on core-model's `EnvStep`: no outside action changes a
program account's owner or data.

No assumption bounds the sender's data (`TransactTx`: signers, accounts, proof, amounts, outputs):
soundness assumes only `PdasDoNotSign` and `CircuitFacts` about it (`REPORT_NOTES.md`).

## Theorems

Labels say why a hypothesis is fair to assume, as in the spec; definitions in `REVIEWING.md`.
**asm** is `[assumption]` (the table above). Every theorem also takes `ProgramNotSystem`,
`HashesAgree`, the syscall contracts and `PairingLaws` (asm); the table lists only what it adds.

| Theorem | Says | Adds | Non-vacuity |
|---|---|---|---|
| `transact_connection` | an accepted `transact` satisfies the spec's | execution + accepted step (premise); `PdasDoNotSign`, `CircuitFacts`, `SameRent` (asm) | `transact_connection_nonvacuous` |
| `run_connection` | an execution is a spec run, or the pool is not initialized | execution (premise); `PdasDoNotSign`, `CircuitFacts` per `transact`, `SameRent` per instruction (asm) | `connection_nonvacuous`, `donation_nonvacuous`, `admin_change_nonvacuous` |
| `transact_complete_except_L1_A0` | what the spec allows, `step` accepts, ending in the spec's `transactEffects` | execution, initialized, `AccountsListed` (premise); `CryptoSucceeds`, `RuntimeFacts`, `PdasOnlyByProgram`, `SameRent` (asm); `SignerIsPlain` (design); not L1, A0 (finding) | `transact_complete_nonvacuous` |
| `run_complete_except_L1_A0` | a spec run is a code execution's run | the deployment's pool (premise); `CryptoSucceeds`, `RuntimeFacts` (asm); no L1, A0 (finding) | `run_complete_nonvacuous` |
| G1a–d, G5a–b `_code` | the goal holds of the execution's run | as `run_connection`; initialized (premise) | `connection_nonvacuous`, `admin_change_nonvacuous` |
| G2a, G4a–b `_code` | the goal holds of every accepted transaction | as `transact_connection` | `transact_connection_nonvacuous` |
| `honestSpendIsAccepted_code` (G3a) | an honest spend is accepted, or a hash break | as `transact_complete`; nothing since the run's last transaction (premise); T1 (asm); `HonestSpend` (owner); `LimitsNotHit` (limit) | `liveness_code_nonvacuous` |
| `adminsCannotLockWithdrawals_code` (G3b) | a withdrawal of `spentAmt ≥ 2` exists, half reaches the recipient, and is accepted | as G3a; no L1 (cannot arise); fewer limits | `liveness_code_nonvacuous` |

The completeness and G3 non-vacuity statements take a 64-bit `usize` (unprovable in Lean). The
build has no `sorry`; check axioms with `#print axioms` (`REVIEWING.md`).

## Findings

Details and recommendations: `FINDINGS.md`. Lean: `Findings.lean`, except I1.

| ID | What | Effect on the results |
|---|---|---|
| L1 | the code rejects `extAmt = 0`, the internal transfer the docs describe | excluded from completeness and G3a; counterexample `transact_complete_fails_for_internal_transfer` |
| A0 | the code rejects a proof whose `proof_a` is 64 zero bytes (the syscalls read it as the identity; arkworks rejects it) | excluded from completeness, G3a, G3b; counterexample `transact_complete_fails_for_zero_proof_a` |
| I1 | only the circuit keeps the two input nullifiers distinct | assumed (`CircuitFacts`); without it `transact_connection` fails (`Proofs/ToyDup.lean`) |
| F7 | a root can be evicted (after about 50 transactions) before an honest proof lands | a limit on G3a (`rootKnown`) |

Where the docs are silent, the spec adds rules marked ADDED MANUALLY; `REPORT_NOTES.md`
("Additions to the documentation") lists them as documentation the authors should add.
