# Notes for the report

Points the final report for the client and external reviewers must cover. Collected while
working; not the report itself.

## How to interpret the results

**Scope.** The connection theorems are safety: whenever the code accepts a `transact`, the spec
allows it, with exactly the spec's effects. It says nothing about transactions the code
rejects. Completeness is checked for the program's own logic (the handler): L1 and A0 are
the only wrong rejections there. Completeness through Anchor and the runtime is future work.

**From steps to executions.** `run_connection` shows every execution of the
code model is a run of the spec, so the spec's invariants (no double spending, every note
backed, only the owner spends, only the authorities change the config) hold for the code.
Between transactions the spec allows what Solana allows: SOL sent to any account (the pool only
gains), other accounts spent from, and admin changes signed by the right authority. The two
Solana details `transact_connection` excludes (a pre-funded nullifier address, a payee that is
a nullifier account) are covered here: they are such allowed changes.

**The run is the execution's own.** `IsRunOf` fixes the spec run to what the execution did:
what `initialize` set up, each transaction, the chain's state and pool balance around each
transaction, and each admin instruction with the signers of its transaction. The one thing it leaves
open mid-run is the balances of other accounts, which can differ for the two Solana details above. So
`adminInstructionsSigned_code` says of the execution's own events that every admin instruction was
signed by the initializer, and a missing signer check would make it false.

**Admins and withdrawals.** G3b shows that after any admin changes, a way to withdraw at least 2
lamports exists, and at least half (rounded down) reaches the recipient; the rest is the fee, which
goes to the recipient the owner chooses. An honest transaction using that way is accepted, unless
another limit of G3a or a hash break blocks it. It needs the limit of 100% on the withdrawal fee rate.
A 1-lamport note can't get out at a 100% rate and a zero fee error margin. A rate raised after a
transaction is built can make its fee too low; the owner then builds another.

**G3 for the code assumes Anchor's account checks pass.** `honestSpendIsAccepted_code` and
`adminsCannotLockWithdrawals_code` say: if the transaction passes Anchor's account checks, `step`
accepts it, or a hash break occurs. They cover Anchor's `init`s, the handler and the lamport check.
Assumed, not machine-checked: the program's accounts are in place, and the four nullifier addresses
meet Anchor's `init` and `SystemAccount` constraints. The second holds for an unspent nullifier
because only the program can create accounts at its derived addresses, and it does so only for
nullifiers it spends, which is visible in `execTransact`. Internal transfers aren't covered (L1), nor
a change in the gap since the last transaction. "Accepted" is by the code model, which leaves out
some of Solana's rejections.

**A difference between code and spec shows up as a theorem that fails.** Lean then proves
the faithful statement false, with a concrete counterexample. No theorem is weakened to make
it provable.

**Assumptions.** Every theorem is only as good as its assumptions: the hash functions compute
the spec's, facts about Solana and the circuit, the syscall contracts, and the Solana details
the spec deliberately leaves out. Each is named and documented in `Hypotheses.lean`.

**Non-vacuity.** A theorem "if H then C" is true but says nothing if H can never hold, and
Lean does not warn about this.
- Results with no hypotheses hold unconditionally: the counterexamples in `Findings.lean`.
- The connection theorems' assumptions are each meant to be true of the real system, and real
  transactions are accepted on chain; core-model's conformance checks compare the model with
  the validator. If every assumption is true and the model is faithful, reality satisfies all
  the hypotheses, so the theorem is not vacuous.
- That argument is about what the assumptions mean. A mistake in how one is written in Lean
  (a formula stronger than intended, or impossible) would slip through. A Lean witness, one
  toy execution where every hypothesis holds, checks the formulas themselves. It exists:
  `connection_nonvacuous`, an execution with a deposit and a withdrawal that spends the
  deposit's note, so the hypotheses also hold together on a real spend.

**What the spec models from the wire.** The spec carries the bytes of the seven public
inputs and of the proof points, and requires canonical encodings, so the check against input
aliasing is a spec requirement the connection proves the code enforces.

**Some goals hold almost by definition.** G4a and G4b follow directly from a precondition and
the effects of the spec's `transact`, and G5a and G5b restate `UpdatedValuesBetweenTransacts.Allowed`. They check that
the spec says what we intend; their value for the code comes entirely from the connection
theorems. The other goals
(G1a–G1d, G2, G3) are consequences that take real proof.

**Spec preconditions not from the docs.** Where the documentation is silent, the spec adds a
rule only if it needs one, marked ADDED MANUALLY (docs silent) (a rule the docs should state)
or SOLANA FACT (how Solana behaves). Each such rule is either enforced by the code (the
connection proves it) or by Solana (proved from the runtime model). Example:
`poolIsSeparate` (the pool is not the signer, the recipient of a withdrawal or the fee
recipient of a non-zero fee) is needed for G1c and G4. The program does not check it;
the runtime's lamport-conservation check enforces it, and the connection proves this from the
model of that check. It is not an assumption of any theorem.

**Completeness.** Handler completeness covers the program's own logic (the extracted
handler), not Anchor's checks or the runtime. It is proved except at L1 and A0.

**Toys.** The spec's and the connection's non-vacuity checks use deliberately broken toy
cryptography (constant or linear hashes, trivial pairing). They show the hypotheses can hold, not that
real cryptography reaches the good outcome.

**How findings surface: an example.** A0 was found because a faithful theorem could not be
proved. Handler completeness without the L1 case got stuck at the verifier's negation step,
and Lean then proved the statement false with a concrete counterexample. Two choices made it
visible: handler completeness (safety cannot see the code rejecting more) and a spec that
models the proof's bytes (so the two decoders became comparable).

## Solana facts in the spec

Solana behaviour the documentation leaves implicit, marked SOLANA FACT in `Spec/Spec.lean`.
Each is how Solana works, not a rule of the program; keep this list in sync with the labels.

- **Only a signature lets an account be debited** (`signerSigned`, `InitParams.initializer_signed`).
  The signer of a `transact` and the initializer of the pool really signed; Anchor's `Signer`
  check enforces both.
- **Rent.** An account must hold a rent-exempt minimum, which grows with its size: the pool's
  (`rentExemptMin`) and a nullifier account's (`nullifierRent`) differ. The pool is created
  holding exactly its minimum; the signer pays one nullifier rent per nullifier account.
- **Zero-filled accounts.** A new account's bytes are zero, so the root history slots other
  than the first hold `0` after initialization (`initTree`).
- **Balances are `u64`** (`balancesFit`). No real transaction is affected: `2^64` lamports
  exceeds the total SOL supply.
- **Encrypted outputs are shorter than `2^32` bytes** (`encOutsFit`). Borsh writes vector
  lengths as `u32`; the transaction size limit (1232 bytes) keeps them far below anyway.
- **The pool is separate from the signer and the payees** (`poolIsSeparate`). A program
  address can't sign, and the runtime rejects an instruction that doesn't conserve lamports.

## Background to the spec's trusted assumptions (T0–T3, `Spec/Statements.lean`)

- T0: circuit = `RelationS` is checked by hand, not mechanised; under-constrained circuits
  are the most common ZK bug class.
- T1: a setup trapdoor has broken a pool before (Zcash Sprout counterfeiting,
  CVE-2019-7167). There is no soundness
  axiom, since perfect soundness is false for Groth16. Reading
  G1a, G1d, G2b as "an attacker can't" needs a reduction that simulates honest proofs
  without their keys and extracts only from the attacker's: weak simulation extractability.
  Groth16's extractor is non-black-box, so extracting all adaptively chosen proofs of a run
  needs a composition argument, which is assumed. Groth16 has knowledge soundness and weak
  simulation extractability in idealized group models: [Gro16] Groth, "On the Size of
  Pairing-based Non-interactive Arguments", EUROCRYPT 2016; [BKSV21] Baghery, Kohlweiss,
  Siim, Volkhov, "Another Look at Extraction and Randomization of Groth's zk-SNARK", FC 2021.
- T2 cannot be a Lean axiom (collisions exist mathematically), so the theorems end in "OR
  this break occurs". Every break compares inputs of one hash function, so no separation
  between them is assumed. `Sha256Collision` is slightly weaker than a plain collision.
- T3 models Poseidon (`H1`–`H4`) as a random oracle. This is a heuristic: Poseidon is also
  computed inside the circuit, where an extractor can't see the queries (precedent: Zcash
  Orchard's Poseidon-based nullifiers). Needed for the "attacker can't" reading of G1a, G1d,
  G2b. `signature` and `nullifier` both use `H3` without domain separation; under this
  model that is fine, since `sk` sits in a different argument position in each and has full
  entropy.

## Additions to the documentation the authors should make

Includes the notes in `FINDINGS.md` ("Notes: behaviour the documentation should state");
keep those in sync. Items that are not findings are listed only here.

- The external amount `−2^63` is rejected.
- The fee rates and the fee error margin are each at most 100%.
- Only the admin key can initialize the pool; deployments must use a build with it set.
- There are two authorities: one over the fee settings, one over the deposit limit.
- Admins can change only the fee settings and the deposit limit (`update_global_config`,
  `update_deposit_limit`).
- Public inputs are canonically encoded (32 big-endian bytes, value below `p`).
- The pool's own address can't be the recipient of a withdrawal or the fee recipient of a
  non-zero fee; the runtime rejects such a transaction.
