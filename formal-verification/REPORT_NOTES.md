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

**Some goals hold by definition.** G1e, G4a and G4b restate a precondition or effect of the
spec's `transact`, and G5 restates `Between.Allowed`. They check that the spec says what we
intend; their value for the code comes entirely from the connection theorems. The other goals
(G1a–G1d, G2, G3) are consequences that take real proof.

**Spec preconditions not from the docs.** Where the documentation is silent, the spec adds a
rule only if it needs one, marked NOT FROM THE DOCS. Each such rule is either enforced by the
code (the connection proves it) or by Solana (proved from the runtime model). Example:
`poolIsSeparate` (the pool is not the signer, the recipient of a withdrawal or the fee
recipient of a non-zero fee) is needed for G1c and G4a. The program does not check it;
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

## Background to the spec's trusted assumptions (T0–T3, `Spec/Statements.lean`)

- T0: a setup trapdoor has broken a pool before (Zcash Sprout counterfeiting,
  CVE-2019-7167). Circuit = `RelationS` is checked by hand, not mechanised; under-constrained
  circuits are the most common ZK bug class. `Groth16Complete` is a hypothesis of G3a only.
- T1: there is no soundness axiom, since perfect soundness is false for Groth16. Reading
  G1a, G1d, G2b, G3b as "an attacker can't" needs a reduction that simulates honest proofs
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
  G2b, G3b. `signature` and `nullifier` both use `H3` without domain separation; under this
  model that is fine, since `sk` sits in a different argument position in each and has full
  entropy.

## Additions to the documentation the authors should make

Includes the notes in `FINDINGS.md` ("Notes: behaviour the documentation should state");
keep those in sync. Items that are not findings are listed only here.

- The external amount `−2^63` is rejected.
- The fee error margin is at most 100%.
- Only the admin key can initialize the pool; deployments must use a build with it set.
- The pool's own address can't be the recipient of a withdrawal or the fee recipient of a
  non-zero fee; the runtime rejects such a transaction.
