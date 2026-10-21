# Notes for the report

Points the final report for the client and external reviewers must cover. Collected while
working; not the report itself.

## How to interpret the results

**Scope.** The main theorem is safety: whenever the code accepts a `transact`, the spec
allows it, with exactly the spec's effects. It says nothing about transactions the code
rejects. The per-function theorems are equations, so they also catch wrong rejections inside
those functions (this is how L1 was found). Handler completeness (the spec's preconditions
hold, so the program's own logic accepts) is planned; completeness through Anchor and the
runtime is future work.

**A difference between code and spec shows up as a theorem that fails.** Lean then proves
the faithful statement false, with a concrete counterexample. No theorem is weakened to make
it provable.

**Assumptions.** Every theorem is only as good as its assumptions: the hash functions compute
the spec's, facts about Solana and the circuit, the syscall contracts, and the Solana details
the spec deliberately leaves out. Each is named and documented in `Hypotheses.lean`.

**Non-vacuity.** A theorem "if H then C" is true but says nothing if H can never hold, and
Lean does not warn about this.
- Results with no hypotheses, or only proved invariants, hold unconditionally: the
  counterexamples, the `check_public_amount` and `validate_fee` theorems, and the invariant
  `wellFormed_reachable`.
- The main theorem's assumptions are each meant to be true of the real system, and real
  transactions are accepted on chain; core-model's conformance checks compare the model with
  the validator. If every assumption is true and the model is faithful, reality satisfies all
  the hypotheses, so the theorem is not vacuous.
- That argument is about what the assumptions mean. A mistake in how one is written in Lean
  (a formula stronger than intended, or impossible) would slip through. A Lean witness, one
  toy execution where `transact` is accepted and every hypothesis holds, checks the formulas
  themselves. State in the report whether it exists.

**What the spec models from the wire.** The spec carries the bytes of the seven public
inputs and of the proof points, and requires canonical encodings, so the check against input
aliasing is a spec requirement the connection proves the code enforces.

**Completeness.** Handler completeness covers the program's own logic (the extracted
handler), not Anchor's checks or the runtime. It is proved except at L1 and A0.

**Toys.** The spec's and the connection's non-vacuity checks use deliberately broken toy
cryptography (constant hashes, trivial pairing). They show the hypotheses can hold, not that
real cryptography reaches the good outcome.

**How findings surface: an example.** A0 was found because a faithful theorem could not be
proved. Handler completeness without the L1 case got stuck at the verifier's negation step,
and Lean then proved the statement false with a concrete counterexample. Two choices made it
visible: handler completeness (safety cannot see the code rejecting more) and a spec that
models the proof's bytes (so the two decoders became comparable).

## Additions to the documentation the authors should make

- The external amount `−2^63` is rejected. Our specification includes this rule; the
  documentation should state it (see `FINDINGS.md`).
