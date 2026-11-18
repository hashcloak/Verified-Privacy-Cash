# Notes for the report

Points the final report for the client and external reviewers must cover. Collected while
working; not the report itself.

## How to interpret the results

**Scope.** Soundness: whenever the code accepts a `transact`, the spec allows it, with exactly
the spec's effects, and every code execution is a spec run (`transact_connection`,
`run_connection`). Completeness: whenever the spec allows a `transact`, the code accepts it,
through Anchor, the handler and the runtime, and ends in the spec's world
(`transact_complete_except_L1_A0`); every spec run is the run of a code execution
(`run_complete_except_L1_A0`), except at findings L1 and A0, the only wrong rejections. Every
result allows an address collision (a break) instead.

**Run completeness covers a few runs Solana cannot produce.** The spec keeps only a
transaction's fee payer (`inputs.s`) off the program's accounts; its other signers, and an admin
change's signers, may be the pool, the tree, the config or a nullifier account. Those are PDAs and
cannot sign on Solana. So `run_complete_except_L1_A0` also covers runs in which a program account
co-signs; for them the code execution it builds is one the code model accepts but Solana would
never produce. This weakens no claim (a larger set of spec runs only makes completeness say more,
and soundness and the goals are unaffected), so the spec has no rule against it.

**From steps to executions.** `run_connection` shows every execution of the
code model is a run of the spec, so the spec's invariants (no double spending, every note
backed, only the owner spends, only the authorities change the config) hold for the code.
Between transactions the spec allows what Solana allows: SOL sent to any account (the program's
accounts, the pool and the nullifier accounts, only gain), other accounts spent from, and admin
changes signed by the right authority.

**Nullifier accounts are modelled.** The spec records a spent nullifier as its nullifier
account (one address per input slot); a nullifier is spent when its account exists in either
slot. The signer pays each new account only what its address is missing to hold the rent, so
pre-funded addresses and payments into nullifier accounts are ordinary balance changes.
`transact_connection` excludes no Solana detail.

**The run is the execution's own.** `IsRunOf` fixes the spec run to what the execution did:
what `initialize` set up, each transaction, the chain's state and pool balance around each
transaction, and each admin instruction with the signers of its transaction. The one thing it leaves
open mid-run is the balances of accounts other than the pool, which the next allowed change sets. So
`onlyAuthoritiesChangeConfig_code` (G5a) says of the execution's own admin instructions that each was
signed by the initializer, and a missing signer check would make it false.

**Admins and withdrawals.** G3b shows that after any admin changes, a way to withdraw at least 2
lamports exists, and at least half (rounded down) reaches the recipient; the rest is the fee, which
goes to the recipient the owner chooses. An honest transaction using that way is accepted, unless
another limit of G3a or a hash break blocks it. It needs the limit of 100% on the withdrawal fee rate.
A 1-lamport note can't get out at a 100% rate and a zero fee error margin. A rate raised after a
transaction is built can make its fee too low; the owner then builds another.

**G3 for the code covers the whole `step`.** `honestSpendIsAccepted_code` and
`adminsCannotLockWithdrawals_code` say: an honest transaction, as the owner submits it
(`ReachesProgram`), is accepted by `step`, or a hash break occurs. Anchor's account checks are
proved to pass: the program's accounts are in place (an invariant of the execution), and the
four nullifier addresses meet Anchor's `init` and `SystemAccount` constraints because the spec
says the nullifiers are unspent. That step assumes only the program creates accounts at its
derived addresses (`PdasOnlyByProgram`; true on Solana, not stated by core-model); otherwise an
address collision occurs. Internal transfers aren't covered (L1), nor
a change in the gap since the last transaction. "Accepted" is by the code model, which leaves out
some of Solana's rejections.

**A difference between code and spec shows up as a theorem that fails.** Lean then proves
the faithful statement false, with a concrete counterexample. No theorem is weakened to make
it provable.

**Assumptions.** Every theorem is only as good as its assumptions: the hash functions compute
the spec's, facts about Solana and the circuit, the syscall contracts, and the Solana details
the spec deliberately leaves out. Each is named and documented in `Hypotheses.lean` (linking the
code to the spec, by-design exclusions) or `CodeModelAssumptions.lean` (about the code alone).

**Hash breaks: properties on named inputs, not computed data.** Collision resistance is never
assumed. As in the spec (T2), a theorem that could fail through a hash collision ends in
"… or a break occurs", where the break names its inputs (e.g. `Sha256Collision a b` for the two
transactions' external data, `AddressCollision` for the seeds one transaction uses), or ranges
over a finite set of the run's own data. This follows the convention of Zcash's Ironwood
verification ("breaks as computed data") in substance, not in form, and the difference is a limit,
not an error:
- **Our breaks are propositions, proved classically.** Ironwood's are data, built by computable
  reductions, so Lean checks that the colliding inputs are produced from the run, not obtained from
  mere existence. Here that rests on an argument: the inputs are the attacker's own data in the run,
  so a violation yields a collision after at most a search over a polynomial-size list.
- **No probability layer.** We stop at "or a break on these inputs"; that such a break is unlikely
  is prose (T2). Ironwood formalises the bound.
Moving to Ironwood's form would mean redesigning the spec's breaks and every theorem using them.

**Non-vacuity.** A theorem "if H then C" is true but says nothing if H can never hold, and
Lean does not warn about this.
- Results with no hypotheses hold unconditionally: the counterexamples in `Findings.lean`.
- The connection theorems' assumptions are each meant to be true of the real system, and real
  transactions are accepted on chain; core-model's conformance checks compare the model with
  the validator. If every assumption is true and the model is faithful, reality satisfies all
  the hypotheses, so the theorem is not vacuous.
- That argument is about what the assumptions mean. A mistake in how one is written in Lean
  (a formula stronger than intended, or impossible) would slip through. A Lean witness, one
  example execution where every hypothesis holds, checks the formulas themselves. It exists:
  `connection_nonvacuous`, an execution with a deposit and a withdrawal that spends the
  deposit's note, so the hypotheses also hold together on a real spend.
- The examples use deliberately broken cryptography (constant or linear hashes, trivial
  pairing). They show the hypotheses can hold, not that real cryptography reaches the good
  outcome.

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
`poolNotRecipient` (the pool is not the recipient of a withdrawal or the fee
recipient of a non-zero fee) is needed for G1c and G4. The program does not check it. For the
payees, the runtime's lamport-conservation check enforces it, and the connection proves this
from the model of that check. For the signer, it follows from the assumed Solana fact that a
program-derived address cannot sign (`PdasDoNotSign`).

**Completeness.** Completeness of `transact` covers the whole `step`: Anchor's account checks,
its `init`s, the handler and the runtime's lamport check; the accepted transaction ends in the
spec's world. It is proved except at L1 and A0. It
excludes, by design, a signer that is not a plain system account (`SignerIsPlain`): Solana rejects
its payments, and the spec does not model account owners. The exclusion is slightly wider than
needed: a signer that pays nothing (a withdrawal whose new nullifier addresses already hold the
rent) may be any account. The code accepts those transactions, so no difference is hidden.

**The sender's data is unrestricted.** The connection theorems put almost no restriction on what
a sender, possibly an attacker, sends in a `transact` (`TransactTx`, `Mapping.lean`): the
signers, the accounts, the proof's bytes and its seven public inputs, the amounts, the fee and
the encrypted outputs. Soundness (`transact_connection`, `run_connection`) assumes only two
things about them:
- no program-derived address signs (`PdasDoNotSign`), a Solana fact;
- the proof does not break the circuit (`CircuitFacts`, finding I1), a cryptographic assumption.
Otherwise the conclusion allows an address collision (a break), but does not assume its absence.
Nothing bounds the values: public inputs `≥ p`, out-of-range amounts and malformed outputs are
all covered. The spec receives the sender's raw bytes (`pubInputBytes`, `π`, the encrypted
outputs), not only their field values, and rejects out-of-range ones (`canonicalInputs`,
`amountRange`, `rootBytesKnown`). So for every input, the code either rejects the transaction or
does exactly what the spec says; in particular it never silently reduces a value mod `p` where
the spec would not. "The code" here is the code model: the extracted program inside
core-model's model of Solana and Anchor (`core-model/README.md` lists what it leaves out).
Completeness adds premises about the transaction as an honest owner submits it (`AccountsListed`,
`SignerIsPlain`) and excludes findings L1 and A0; it is about the transactions the spec allows,
not about attacks.

**What completeness over runs adds.** The safety goals (G1, G2, G4, G5) cannot see the code
rejecting a step the spec allows between transactions: if `initialize` rejected a valid initial
config, or `update_global_config` always failed, every goal would still hold.
`run_complete_except_L1_A0` rules this out: every spec run, with its initial config, admin
changes and outside actions, is the run of a code execution, up to L1, A0 and address
collisions. It also shows that core-model's outside actions (`EnvStep`) can make every change the
spec allows between transactions, so the code model leaves out none of them.

**How findings surface: an example.** A0 was found because a faithful theorem could not be
proved. Completeness of the handler without the L1 case got stuck at the verifier's negation step,
and Lean then proved the statement false with a concrete counterexample. Two choices made it
visible: completeness (safety cannot see the code rejecting more) and a spec that
models the proof's bytes (so the two decoders became comparable).

## Solana facts in the spec

Solana behaviour the documentation leaves implicit, marked SOLANA FACT in `Spec/Spec.lean`.
Each is how Solana works, not a rule of the program; keep this list in sync with the labels.

- **Only a signature lets an account be debited** (`signerSigned`, `InitParams.initializer_signed`).
  The signer of a `transact` and the initializer of the pool really signed; Anchor's `Signer`
  check enforces both.
- **Rent.** An account must hold a rent-exempt minimum, which grows with its size: the pool's
  (`rentExemptMin`), a nullifier account's (`nullifierRent`), the tree's and the config's
  (`InitParams.treeRent`, `configRent`) differ. `initialize` creates the pool, the tree's and the
  config's accounts holding exactly their minimum (`initWorld`; SOL sent there earlier counts as
  sent before the first transaction); the signer pays each new nullifier account what its address
  is missing to hold the rent (`nullifierTopUp`): anyone can send lamports to an address before
  an account exists there.
- **Nullifier accounts** (`State.nullifierAccounts`, `nullifierAddr`). A spent nullifier is an
  account at a program-derived address, one per input slot; only the program creates such an
  account, and it never closes one, so the accounts stay between transactions.
- **The program's accounts only gain between transactions** (`Allowed.programAccountsGain`).
  Only an account's owner can debit it; the program owns the pool, the nullifier accounts and
  the tree's and config's accounts (`State.IsProgramAccount`, `State.treeAccount`,
  `configAccount`), and debits nothing outside `transact`. Without this, a nullifier
  account could be drained to 0 lamports, which Solana deletes, re-opening its note.
- **Anchor's `init` fails where an account exists** (`nullifierAccountsCreatable`): the two
  new nullifier accounts are none of the program's accounts and not each other.
- **Zero-filled accounts.** A new account's bytes are zero, so the root history slots other
  than the first hold `0` after initialization (`initTree`).
- **Balances are `u64`** (`balancesFit`; every balance between transactions,
  `Allowed.balancesFit`, and at the start, `InitParams.balances_fit`). No real
  transaction is affected: `2^64` lamports exceeds the total SOL supply.
- **Encrypted outputs are shorter than `2^32` bytes** (`encOutsFit`). Borsh writes vector
  lengths as `u32`; the transaction size limit (1232 bytes) keeps them far below anyway.
- **Program-derived addresses can't sign** (`signerNotPoolNotNullifiers`): the signer is none of
  the program's accounts (the pool, the nullifier accounts, the tree's and config's accounts) and not a new nullifier
  account. Likewise the initializer is none of the three accounts `initialize` creates
  (`InitParams.initializer_not_created`).
- **The pool is not paid as a payee** (`poolNotRecipient`). The runtime rejects an instruction
  that doesn't conserve lamports.

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

These are not defects. The code makes a reasonable choice that the documentation does not
mention, so users and integrators cannot know it. Where the spec needs such a rule, it includes
it, marked ADDED MANUALLY (docs silent).

- **The external amount `−2^63` is rejected.** The external amount is an `i64`, whose range
  is `−2^63` to `2^63 − 1`. Negating `−2^63` overflows, so `check_public_amount` and
  `validate_fee` reject it. This is reasonable: `2^63` lamports is about 9.2 billion SOL,
  more than the total SOL supply, so no real withdrawal is affected. Our specification
  includes this rule, but it is not in the documentation, which should state it.
- **The fee error margin is at most 100%.** `update_global_config` refuses a fee error margin
  above 10000 basis points. Our specification includes this rule, because its fee rule computes
  `10000 − feeErrorMargin`; the documentation gives the default (5%) but no bound, and should
  state it.
- **The fee rates are at most 100%.** `update_global_config` refuses a deposit or withdrawal fee
  rate above 10000 basis points. Our specification includes this rule, because without it admins
  could set a rate that locks notes in the pool; the documentation gives defaults but no bound,
  and should state it.
- **The initial settings are always the defaults.** `initialize` takes no settings: it sets the
  deposit limit to 1000 SOL, the deposit fee rate to 0%, the withdrawal fee rate to 0.25% and the
  fee error margin to 5%. Only `update_global_config` and `update_deposit_limit` change them
  afterwards. The documentation lists these values as defaults but doesn't say that initialization
  always uses them. Our specification includes this rule; the documentation should state it.
- **The deposit limit is a `u64`.** `update_deposit_limit` takes the new limit as a `u64`, so
  it is below `2^64` lamports. No real deposit is affected. Our specification includes this rule;
  the documentation should state it.
- **Only the admin key can initialize the pool.** `initialize` checks the caller against a
  hard-coded admin key; whoever initializes becomes the authority over fees and the deposit
  limit. In the localnet and test builds there is no admin key, so anyone can initialize.
  Our specification includes this rule; the documentation should state it, and that deployments
  must use a build with the admin key set.
- **Two authorities: one over the fee settings, one over the deposit limit.** The global
  config's authority may change the fees (`update_global_config`); the Merkle tree's authority
  may change the deposit limit (`update_deposit_limit`). `initialize` sets both to the
  initializer, and nothing changes them afterwards. Our specification includes this rule; the
  documentation should state who controls what.
- **Admins can change only the fee settings and the deposit limit.** No other setting has an
  admin instruction: `update_global_config` covers the fee rates and the fee error margin, and
  `update_deposit_limit` covers the deposit limit. Our specification includes this rule; the
  documentation should state what admins can change.
- **Public inputs must be canonically encoded.** Each of the seven public inputs is 32
  big-endian bytes whose value must be below the field modulus `p`; the code rejects larger
  values. Without this, `x` and `x + p` would be two encodings of the same field element, so
  one nullifier could be sent as two different byte strings. Our specification includes this
  rule; the documentation should state the wire format.
- **The sender chooses the fee recipient, by design.** `fee_recipient_account` can be any
  account; the program checks only that it matches the external data hash and that the fee
  meets the minimum. A sender can therefore pay the fee to themselves, which avoids the
  protocol fee. The client confirmed this is intentional, for decentralization (Zigtur,
  Kriko); Veridise recommends documenting it. Our specification leaves the fee recipient
  unconstrained, as the code does; the documentation should state this.
- **A SOL-pool transaction names the SOL mint.** The program hashes the external data with the
  mint `11111111111111111111111111111112` (`SOL_ADDRESS`), so a transaction whose external data
  names another mint fails the external data check. Our specification includes this rule
  (`mintIsSol`), with the SOL mint left to the deployment (`Deployment.solMint`);
  the documentation should state the rule and the value.
- **The pool can't pay itself.** The pool's own address can't be the recipient of a withdrawal
  or the fee recipient of a non-zero fee; the runtime rejects such a transaction. The
  documentation should state it.
