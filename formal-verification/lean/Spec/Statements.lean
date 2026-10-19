import Spec.NonVacuity

/-! # Privacy Cash: security goals and theorem statements

This file is what reviewers read. It holds the security goals, the trusted assumptions, and
every theorem *statement*, each proved by pointing at its proof in `Spec/Proofs.lean`; Lean
checks that the statement here is exactly what was proved. Reviewers don't need the proofs.

## How to review

1. This file: the goals, the trusted assumptions, and each statement with its docstring.
2. The definitions the statements use: `Spec/Vocabulary.lean` (runs, notes, breaks, the
   pieces of G3a) and, for the model itself, `Spec/Spec.lean` (state, `transact` and its
   preconditions, `initWorld`).
3. The non-vacuity statements at the end of this file: they show the hypotheses can hold.
4. `Spec/Axioms.lean`: the build fails if any theorem uses `sorry` or an extra axiom.

**Where the security argument lives.** Every theorem says "the property holds, OR a named
hash break occurs at specific values". That is only as strong as the trusted assumptions
T0–T3 below, which are prose, not Lean. They are the part that needs a cryptographer's
review. For the theorems that end in a break (G1a–G1d, G2a, G2b, G3a, G3b), the title means
"..., unless a named hash break occurs", which T2 makes infeasible. G1e, G3c, G4a, G4b and
G5 have no break: they hold outright.

## Who controls each hypothesis

Every hypothesis of every theorem is tagged:
- `[attacker]`: chosen by an attacker; quantified over all choices.
- `[owner]`: chosen by the honest owner (honest construction).
- `[premise]`: the situation the theorem is about (e.g. "this note is unspent").
- `[policy]`: a program policy check; it can legitimately block a transaction.
- `[limit]`: a protocol limit; it can legitimately block (root window, tree capacity).
- `[trust Tn]`: a trusted assumption, see below.
A fact about the state that is none of these is a bug: it must be derived, not assumed.

## Where the goals come from

Privacy Cash is a Zerocash-style shielded pool: notes are commitments in a Merkle tree, a
spend reveals nullifiers, and a Groth16 proof shows the spend is valid. The security
definition for such schemes is taken from

  [ZC] Ben-Sasson et al., "Zerocash: Decentralized Anonymous Payments from Bitcoin",
       IEEE S&P 2014, §3.4 and Appendix C.

[ZC] calls a scheme secure if it has ledger indistinguishability (privacy), transaction
non-malleability and balance. The Privacy Cash docs ("How it works", Security properties)
claim: transaction privacy, double-spend prevention, amount integrity. A pool must also let
owners withdraw, pay out correctly and keep its configuration; [ZC] does not cover these.

  Goal                          Source                                          Theorems
  G1 Balance                    [ZC] Balance; docs: double-spend prevention,    G1a–G1e
                                amount integrity
  G2 Non-malleability           [ZC] Transaction non-malleability               G2a G2b
  G3 Liveness                   ours: funds must not get stuck                  G3a G3b G3c
  G4 Correct public payouts     docs: amount integrity                          G4a G4b
  G5 Config immutability        ours                                            G5
  -  Privacy                    [ZC] Ledger indistinguishability; docs          out of scope

G1 Balance: nobody can end up with more value than they put in.
G2 Non-malleability: a transaction someone has seen can't be altered or front-run.
G3 Liveness: an honest owner can spend; nobody can block it; when the pool freezes.
G4 Correct public payouts: public SOL moves exactly as specified.
G5 Config immutability: transactions can't change the pool's configuration.
Each theorem's title and explanation are in its docstring below (and only there).

The informal list in `Spec/theorems.lean` maps as: no double spending, no replay -> G1b;
value cannot be inflated, only deposited coins can be withdrawn -> G1c; proof binding ->
G2a; only the owner can spend -> G1d, G1e and G2b; unspent notes can be spent -> G3a and G3b;
notes cannot be forged -> G1a.

## How a goal becomes a theorem

[ZC] states each goal as a game: no efficient adversary wins except with negligible
probability, proved by reduction to the primitives. Here a theorem says: for every
sequence of accepted transactions (a `Run`), whatever inputs and witnesses were used, the
property holds OR a named hash break occurs (`H1Collision`, `H2Collision` via
`PathCollision`, `H2ZeroPreimage`, `H3Collision`, `H4Collision`, `H4ZeroPreimage`,
`Sha256Collision`). Whoever violates the property hands over that break.

A theorem can look strong and still say nothing. Every statement is checked for these
four ways that happens:
  - It must be about what actually happened. Bad: "there is some list of transactions
    whose amounts add up to the pool balance" (one made-up transaction with the right
    amount satisfies it). Good: "the transactions that were actually applied add up to
    the pool balance". So lists, tree leaves and indices always come from the `Run`.
  - A hash break must be at specific values. Bad: "... or there are two inputs with the
    same hash" (for a real hash such inputs always exist, so this is always true). Good:
    "... or these two values, computed from the transactions, have the same hash".
  - Whatever an attacker controls (transaction inputs, witnesses) is "for all", never
    "there exists": the property must hold whatever the attacker picks.
  - Facts about the state are proven from the state, not assumed (see the tags above).

## Runs and witnesses

Theorems quantify over a `Run` (`Spec/Vocabulary.lean`): the transactions actually applied
from `initWorld`, and the world before each. Every reachable world ends some run
(`ReachableWorld.exists_run`), so nothing is lost, and the code connection
(`ReachableWorld`) still applies. Witnesses are any `wit` with `r.WitnessesFor wit`, read
as what a knowledge extractor gets from whoever made the proofs (T1). The theorems hold
for every such choice.

## Trusted assumptions

T0 Deployment. What every theorem silently relies on, and what has actually broken
   shielded pools:
   - the trusted setup was honest, so `Deployment.vk` has no known trapdoor (cf. the
     Zcash Sprout counterfeiting bug, CVE-2019-7167), and the verification key in the
     program is the one the setup produced. Groth16 completeness for that key
     (`Groth16Complete`, a hypothesis of G3a only) follows from this;
   - the circom circuit enforces exactly `RelationS`. This is checked by hand, not
     mechanised; an under-constrained circuit is the most common ZK bug class;
   - nobody can replace the program (upgrade authority), or the theorems are moot;
   - the pool started from `initWorld` (no migration or re-initialization since);
   - the Solana runtime behaves as modelled: a transaction applies fully or not at all,
     every instruction conserves lamports (`poolIsSeparate` relies on this), and the
     per-slot nullifier accounts act as one nullifier set.
T1 Groth16 extraction. There is no soundness axiom: perfect soundness ("a verifying proof
   implies a witness exists") is false for Groth16. Instead, every theorem about a run
   takes as given a witness for each transaction whose proof verifies (`r.WitnessesFor
   wit`; G1e makes that every accepted transaction). Whose witnesses these are matters:
   for an honest user's transaction, `wit` is that user's real witness; for an attacker's,
   it is what an extractor computes from the attacker. The reduction behind "an attacker
   can't" must simulate honest users' proofs without knowing their keys, and extract only
   from the attacker's proofs. That is weak simulation extractability: an attacker who has
   seen honest proofs can still only make proofs for new public inputs if it knows a
   witness. G1a, G1d, G2b and G3b need it for their "attacker can't" reading. A run has many
   adaptively chosen proofs, and Groth16's extractor is non-black-box, so extracting all of
   them needs a composition argument that is assumed here, not given. Groth16 has knowledge
   soundness and weak simulation extractability in idealized group models: [Gro16] Groth,
   "On the Size of Pairing-based Non-interactive Arguments", EUROCRYPT 2016; [BKSV21]
   Baghery, Kohlweiss, Siim, Volkhov, "Another Look at Extraction and Randomization of
   Groth's zk-SNARK", FC 2021.
T2 Hash functions: finding an `H1`, `H2`, `H3` or `H4` collision, an `H2` or `H4`
   preimage of `0`, or two byte strings whose `sha256` digests are equal after reducing
   mod `p` (`Sha256Collision`, slightly weaker than a plain `sha256` collision) is
   infeasible. This can't be an axiom in Lean (collisions exist mathematically), so the
   theorems instead end in "OR this specific break occurs"; T2 is what makes that branch
   impossible in practice. Every break compares inputs of the same hash function (`H3`
   with `H3`, `H4` with `H4`), so no separation between the hash functions is assumed.
T3 Keys. Owners sample their secret keys uniformly at random and keep them secret. The
   same secret key `sk` goes into the public key `H1 sk` (inside every commitment to the
   owner) and, through `signature = H3 sk c idx`, into every nullifier the owner reveals.
   So what one of these values leaks about `sk` matters for the other: the assumption is
   that, together, they reveal nothing usable about `sk`. Concretely, Poseidon (`H1`–`H4`)
   is modelled as a random oracle. This is a heuristic: Poseidon is also computed inside
   the circuit, where an extractor can't see those hash queries. There is precedent: Zcash
   Orchard's nullifier function is Poseidon-based. Needed to read G1a, G1d, G2b and G3b as
   "an attacker can't": they show the spender's key is the owner's, and T3 says only the
   owner knows it. `signature` and `nullifier` both use `H3` with no domain separation;
   under this model that is fine, because the secret key sits in a different argument
   position in each and has full entropy.

## Where the proof check enters

The theorems about a run get each transaction's witness from `r.WitnessesFor wit`, which
gives a witness only for transactions whose proof verifies (`proofValid`). Every accepted
transaction's proof verifies (G1e, the `validZKP` precondition), so the witnesses cover
the whole run. A program that skipped the proof check would not satisfy G1e, and the
theorems would no longer apply to its transactions. That the code's verifier really
computes `proofValid` is the connection's Groth16 verifier bridge (not built yet).

## Checks against goals

Each check of `transact` and constraint of `RelationS`, and the theorem whose proof uses
it. A check no theorem uses protects something not stated yet, or is redundant.

  knownRoot                                                 G1a
  treeNotFull                                               G1a, G3c
  newNullifiers                                             G1b
  pubAmtConsistency                                         G1c
  poolSolvency, poolSeparate                                G1c, G4a, G4b
  amountRange                                               G1c, G2a
  externalDataBinding                                       G2a
  signerSolvency                                            G4a, G4b
  encOutLength                                              G2a
  RelationS: outputCommitmentIntegrity, correctOpenings     G1a
  RelationS: nullifierCorrectness                           G1b, G2b, G3b
  RelationS: noDuplicateNullifiers                          G1b
  RelationS: amountConservation, outputRangeChecks          G1c
  validZKP                                                  G1e; through it G1a–G1d,
                                                            G3a, G3b
  minimumFee, depositLimit       none: operator rules (fee income, deposit cap); they
                                 protect no user's funds
  distinctNullifiers             none: duplicates `RelationS.noDuplicateNullifiers`. The
                                 program relies on the circuit for it, as we do (T1)

## Out of scope

  - Privacy: needs a probabilistic model.
  - Config-update instructions (`update_global_config`, `update_deposit_limit`): only
    `transact` is modeled, so G5 says nothing about their authority checks.
  - SPL tokens: SOL only for now. For later: `mint` is private in the circuit and is not
    linked to `mintAddr`, so asset separation must come from per-mint trees and the global
    nullifier set, not from the note's `mint`.
  - Solana network fees: charged by the runtime before the program runs, so `balances` are
    the balances the program sees.

## Known gaps

  - The program doesn't check that the recipient and fee recipient are not the pool; it
    relies on Solana's runtime to reject those transactions (`poolIsSeparate`). A finding
    to report.
  - A root stays in the history for about 50 transactions (100 slots, two roots per
    transaction); G3a needs the spend's root to still be there.
  - G1e, G4a, G4b and G5 follow from how `transact` is defined. They say something about
    the code only through the connection.
  - Deposits with a fee: the spec checks the pool balance before the deposit lands, the
    code after (`hDevPool`, `CONNECTIONS.md`). G3a keeps this check as a hypothesis.

-/

namespace LeanSpec.Goals
open LeanSpec PoseidonHashes Sha

variable [PoseidonHashes] [Sha] [Groups]
variable [AddCommGroup G1] [Module F G1] [AddCommGroup G2] [Module F G2] [CommGroup GT]
variable [Pairing] [Deployment]

/-! ## G1. Balance -/

/-- **G1a. Nobody can spend a note that doesn't exist, isn't theirs, or for more than it holds.**
    Guards against: spending a made-up note, someone else's note, or a real note with a
    larger amount than it was created with.

    How it is stated: for every sequence of accepted transactions (a `Run`) and every
    witness behind their proofs (`wit`), each non-zero input of transaction `j` opens a
    tree leaf created by an earlier transaction, and the input note (amount, owner key,
    blinding, mint) equals the note created there. Otherwise a hash break occurs
    (`SpendBreak`).

    Why this is the right statement: each of the three attacks makes the spent note differ
    from the note stored at the leaf it opens. Equal owner keys mean the spender's secret
    key hashes to the owner's public key. The leaf contents are taken from the accepted
    transactions themselves, not chosen freely. -/
theorem spends_are_genuine
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)        -- [trust T1] the witnesses of its proofs
    (j : ℕ) (hj : j < r.txs.length) (i : Fin 2)            -- [premise] any input of any transaction
    (hne : (wit j).inAmt i ≠ 0) :                          -- [premise] ...that spends a note
    (spentLeaf wit j i < 2 * j ∧ (wit j).inNote i = leafNote wit (spentLeaf wit j i))
    ∨ SpendBreak r wit j i :=
  LeanSpec.spends_are_genuine params r wit hwit j hj i hne

/-- **G1b. No note is spent twice.**
    Guards against: spending the same note again, in a later transaction or twice within
    one transaction.

    How it is stated: in any `Run`, two different non-zero inputs (`(j, i) ≠ (j', i')`) never
    open the same tree leaf, unless a hash break occurs (`SpendBreak` for one of them, or an
    `H1` collision between their secret keys).

    Why this is the right statement: by G1a every spend opens the leaf holding exactly the
    note it spends, so "a note is spent twice" means "two inputs open the same leaf". The
    two inputs are any pair in the run, so both later and same-transaction re-spends are
    covered. -/
theorem no_double_spend
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)        -- [trust T1] the witnesses of its proofs
    (j j' : ℕ) (hj : j < r.txs.length) (hj' : j' < r.txs.length) (i i' : Fin 2)
                                                           -- [premise] any two inputs...
    (hne : (wit j).inAmt i ≠ 0) (hne' : (wit j').inAmt i' ≠ 0)   -- [premise] ...that spend notes
    (hdiff : (j, i) ≠ (j', i'))                            -- [premise] ...and are different
    (hsame : spentLeaf wit j i = spentLeaf wit j' i') :    -- [premise] ...at the same position
    SpendBreak r wit j i ∨ SpendBreak r wit j' i'
      ∨ H1Collision ((wit j).inSk i) ((wit j').inSk i') :=
  LeanSpec.no_double_spend params r wit hwit j j' hj hj' i i' hne hne' hdiff hsame

/-- **G1c. Every unspent note is fully backed by SOL in the pool.**
    Guards against: value created from nothing (inflation), which would leave the pool
    unable to pay out all notes; and SOL disappearing from the pool.

    How it is stated: in any `Run`, the pool's SOL equals its rent reserve plus the total
    value of the notes not yet spent, or a hash break of G1a/G1b occurs (`BalanceBreak`). A note's value comes from the witness of the transaction
    that created it; "not yet spent" means no non-zero input opened its leaf.

    Why this is the right statement: inflation is private value exceeding the SOL that
    backs it, so the two are compared directly. An equality rules out both directions. -/
theorem balance
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    (r.final.poolBalance : ℤ) = params.rentExemptMin + ∑ pos ∈ r.unspent wit, leafValue wit pos
    ∨ BalanceBreak r wit :=
  LeanSpec.balance params r wit hwit

/-- **G1d. Only the owner's secret key can spend a note.**
    Guards against: someone other than the owner spending the owner's note.

    How it is stated: in any `Run`, if a non-zero input of transaction `j` opens a note
    whose owner public key is `H1 skOwner`, that input's secret key is `skOwner`, unless the
    spend exposes a `SpendBreak` or `skOwner` and the input's key collide under `H1`.

    Why this is the right statement: it is the per-owner property the docs claim, which
    the pool-wide G1c does not give (a theft that keeps totals unchanged passes G1c). It
    follows from G1a. Reading it as "only the owner *can* spend" needs T1 (whoever made the
    proof knows the witness, so knows `skOwner`) and T3 (`skOwner` can't be found from the
    public data). -/
theorem honest_note_spent_only_with_owner_key
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)        -- [trust T1] the witnesses of its proofs
    (j : ℕ) (hj : j < r.txs.length) (i : Fin 2)            -- [premise] any input of any transaction
    (hne : (wit j).inAmt i ≠ 0)                            -- [premise] ...that spends a note
    (skOwner : F)                                          -- [premise] ...owned by `skOwner`:
    (hOwner : (leafNote wit (spentLeaf wit j i)).ownerPk = H1 skOwner) :   -- [premise]
    (wit j).inSk i = skOwner ∨ SpendBreak r wit j i ∨ H1Collision skOwner ((wit j).inSk i) :=
  LeanSpec.honest_note_spent_only_with_owner_key params r wit hwit j hj i hne skOwner hOwner

/-- **G1e. A transaction is accepted only with a proof that verifies.**
    Guards against: a program that accepts a spend without checking its proof, so that
    anyone can spend without knowing the note's secrets.

    How it is stated: if the transaction's proof doesn't verify for its public inputs
    (`proofValid`), `transact` fails.

    Why this is the right statement: knowledge of a note's secrets is shown only by the
    proof, so a spend that skips the check needs no knowledge at all. G1a–G1d, G3a and G3b
    depend on the same precondition (`validZKP`): they get each transaction's witness from
    `r.WitnessesFor wit`, which gives one only for transactions whose proof verifies
    (`WitnessesFor.relation`). Like G4 and G5, G1e follows from how `transact` is defined:
    it guarantees the spec checks the proof; that the code does is the connection's
    verifier bridge. -/
theorem transact_requires_valid_proof
    (oldWorld newWorld : World) (inputs : TxInputs)        -- [attacker] any transaction
    (h : ¬ proofValid inputs) :                            -- [premise] whose proof doesn't verify
    ¬ transact inputs oldWorld newWorld :=
  LeanSpec.transact_requires_valid_proof oldWorld newWorld inputs h

/-! ## G2. Non-malleability -/

/-- **G2a. A copied proof can't redirect the payout.**
    Guards against: an attacker who sees an honest transaction, reuses (or re-randomizes)
    its proof, and changes the recipient, amount, fee, fee recipient, encrypted outputs or
    token.

    How it is stated: if the honest transaction `T` (as observed: well formed) and an
    accepted transaction `T'` have the same public inputs, they have the same recipient,
    amount, fee, fee recipient, token and encrypted outputs, unless `sha256` collides on
    their external data.

    Why this is the right statement: re-randomizing a Groth16 proof needs no secrets but
    keeps the public inputs, and those include the hash of the external data. `T` is only
    observed, not accepted: once `T'` is accepted, `T` fails, since they share nullifiers.
    The amounts and lengths are in range (`amountsInRange`, `encOutsFit`), so the encoding
    determines every field. Not bound: the signer `s`; replacing it only changes who pays
    for a deposit. A proof for *new* public inputs is G2b. -/
theorem same_public_inputs_same_external_data
    (T : TxInputs)                                         -- [premise] the honest transaction, seen
    (hT : externalDataBound T ∧ amountsInRange T.extAmt T.f ∧ encOutsFit T)
                                                           -- [premise] ...well formed
    (T' : TxInputs) (oldWorld' newWorld' : World)          -- [attacker] the attacker's transaction
    (h' : transact T' oldWorld' newWorld')                 -- [attacker] ...accepted
    (hSame : T.pubInputs = T'.pubInputs) :                 -- [premise] ...with the same public inputs
    (T.A = T'.A ∧ T.extAmt = T'.extAmt ∧ T.encOut0 = T'.encOut0 ∧ T.encOut1 = T'.encOut1
      ∧ T.f = T'.f ∧ T.t = T'.t ∧ T.mintAddr = T'.mintAddr)
    ∨ Sha256Collision (serealizeExternalData T) (serealizeExternalData T') :=
  LeanSpec.same_public_inputs_same_external_data T T' oldWorld' newWorld' hT h' hSame

/-- **G2b. Front-running a spend requires the owner's secret key.**
    Guards against: an attacker who sees an honest transaction and submits their own
    transaction spending the same note (same nullifier), e.g. paying themselves.

    How it is stated: if two witnesses (each satisfying the circuit) reveal the same
    nullifier, they contain the same secret key, unless `H3`, `H4` or `H1` collide on
    values from the two witnesses.

    Why this is the right statement: a valid proof for new public inputs requires knowing
    a witness for it (T1). By this theorem that witness holds the honest owner's secret
    key, which the attacker doesn't have. -/
theorem shared_nullifier_requires_owner_key
    (x : PubInputs) (w : Witness) (hRel : RelationS x w)   -- [premise] the honest transaction's
                                                           --   statement and its owner's witness
    (x' : PubInputs) (w' : Witness)                        -- [attacker] the attacker's statement
    (hRel' : RelationS x' w')                              -- [trust T1] ...and the witness extracted
                                                           --   from the attacker (weak sim. extract.)
    (i i' : Fin 2)
    (hShared : x.nullifiers i = x'.nullifiers i') :        -- [premise] they reveal the same nullifier
    w'.inSk i' = w.inSk i
    ∨ H3Collision (w.nullifierArgs i) (w'.nullifierArgs i')
    ∨ H4Collision (w.inNote i) (w'.inNote i')
    ∨ H1Collision (w.inSk i) (w'.inSk i') :=
  LeanSpec.shared_nullifier_requires_owner_key x x' w w' hRel hRel' i i' hShared

/-! ## G3. Liveness -/

/-- **G3a. An honest owner's spend is accepted, unless a policy check blocks it or a hash
    break occurs.**
    Guards against: funds getting stuck because the program rejects an honest owner: on
    the proof, the root, the Merkle path, an already-used nullifier, or pool solvency.

    How it is stated: after any `Run`, an owner spends notes it owns that are still unspent
    (`OwnsUnspentNotes`), against a root still in the history (`RootInWindow`), with a
    transaction built honestly (`BuiltHonestly`). If the policy checks pass
    (`PolicyChecksPass`), the program accepts the transaction (`CanBeAccepted`), unless an
    attacker-side hash break occurs (`LivenessBreak`).

    Why this is the right statement: "nullifier not yet used", "pool can pay", "the root is
    known" and "a proof exists" are derived (G3b, G1c, Groth16 completeness), not assumed.
    Every hypothesis is tagged with who controls it. The ones that can legitimately block
    a spend are the policy checks and the two limits: the root window and the tree's
    capacity (G3c). One policy check is stricter than the code (`hDevPool`). -/
theorem unspent_note_is_spendable
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (hCompl : Groth16Complete)                             -- [trust T0] Groth16 completeness
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)        -- [trust T1] the witnesses of its proofs
    (inputs : TxInputs) (witness : Witness) (k : ℕ)        -- [owner] the owner's transaction, its
                                                           --   secrets, the tree state it uses
    (hRoot : RootInWindow r inputs.R k)                    -- [owner], [limit]: see the structure
    (hNotes : OwnsUnspentNotes r wit witness k)            -- [premise], [owner]: see the structure
    (hHonest : BuiltHonestly r.final inputs witness)       -- [owner]
    (hPolicy : PolicyChecksPass r.final inputs) :          -- [policy], [limit]: see the structure
    CanBeAccepted inputs r.final ∨ LivenessBreak r wit witness k :=
  LeanSpec.unspent_note_is_spendable params hCompl r wit hwit inputs witness k hRoot hNotes
    hHonest hPolicy

/-- **G3b. Nobody can block an unspent note.**
    Guards against: an attacker making an owner's note unspendable by using up its
    nullifier first, e.g. with a zero-amount ("dummy") input, which needs no Merkle path.

    How it is stated: for any `Run`, any witnesses `wit`, and any note with non-zero amount
    that no spend of the run has opened (`pos ∈ r.unspent wit`), the note's nullifier is not
    yet in the nullifier set, unless an `H3` or `H4` collision occurs (`NullifierTaken`).

    Why this is the right statement: blocking a note means its nullifier is spent while the
    note itself was never spent. Equal nullifiers mean equal commitment, position and
    signature (or an `H3` collision), and an equal commitment means an equal note, amount
    included (or an `H4` collision). So the other input would be a non-zero spend of the
    same note at the same position, which `pos ∈ r.unspent wit` excludes. Binding the
    position into the nullifier is what defeats the "Faerie Gold" attack (Zcash Protocol
    Specification §8.4). -/
theorem unspent_note_cannot_be_blocked
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)        -- [trust T1] the witnesses of its proofs
    (w : Witness) (i : Fin 2)                              -- [owner] the owner's secrets, input `i`
    (hne : w.inAmt i ≠ 0)                                  -- [premise] ...a real note
    (hpos : (w.openings i).index.val ∈ r.unspent wit) :    -- [premise] ...that is unspent
    nullifier (w.inC i) (w.sign i) (w.openings i).index ∉ r.final.state.nullifiers
    ∨ NullifierTaken r wit w i :=
  LeanSpec.unspent_note_cannot_be_blocked params r wit hwit w i hne hpos

/-- **G3c. A full tree freezes the pool (a finding, not a guarantee).**
    Guards against: nothing; this records a limitation. Every transaction appends two
    notes, so once the tree is full, no transaction can succeed, withdrawals included, and
    every unspent note is locked for good.

    How it is stated: after any `Run` of at least `2^25` transactions (`2^26` leaves, the
    tree's capacity), no transaction is accepted.

    Why this is the right statement: it shows exactly when liveness (G3a) ends. -/
theorem full_tree_freezes_pool
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (hfull : 2^25 ≤ r.txs.length)                          -- [premise] ...of at least 2^25 transactions
    (inputs : TxInputs) (newWorld : World) :               -- [attacker] any next transaction
    ¬ transact inputs r.final newWorld :=
  LeanSpec.full_tree_freezes_pool params r hfull inputs newWorld

/-! ## G4. Correct public payouts -/

/-- **G4a. No SOL is created or lost, except the nullifier rent.**
    Guards against: a transaction that changes the total SOL held by the pool and the
    accounts it touches, other than by the rent for the two new nullifier accounts.

    How it is stated: in one accepted transaction, the pool, the signer, the recipient and
    the fee recipient (counted once each, even if some coincide) end with exactly their
    total before, minus twice the nullifier rent (`nullifierRent`). Every other account is
    unchanged (G4b).

    Why this is the right statement: conservation is about totals, so it is stated over
    every account the transaction touches at once, whatever roles coincide. The pool is
    an ordinary account here, as on Solana. The rent goes to the two new nullifier
    accounts, which are not tracked in `balances`. -/
theorem no_sol_created
    (oldWorld newWorld : World) (inputs : TxInputs)        -- [attacker] any transaction
    (h : transact inputs oldWorld newWorld) :              -- [premise] ...accepted
    ∑ k ∈ ({inputs.s, inputs.A, inputs.t, oldWorld.state.pool} : Finset Pubkey),
        (newWorld.balances k : ℤ)
    = ∑ k ∈ ({inputs.s, inputs.A, inputs.t, oldWorld.state.pool} : Finset Pubkey),
        (oldWorld.balances k : ℤ)
      - 2 * oldWorld.nullifierRent :=
  LeanSpec.no_sol_created oldWorld newWorld inputs h

/-- **G4b. Every account gets exactly what it is owed and pays exactly what it owes.**
    Guards against: the recipient or fee recipient being paid the wrong amount, the signer
    being charged the wrong amount (in particular a deposit the signer doesn't pay for),
    the pool gaining or losing the wrong amount, and any uninvolved account being touched.

    How it is stated: in one accepted transaction, every account changes by exactly
    `balanceDelta`: `|extAmt|` to the recipient on a withdrawal, `f` to the fee recipient,
    `extAmt` and twice the nullifier rent from the signer, `extAmt − f` to the pool, summed
    if roles coincide, and nothing for anyone else.

    Why this is the right statement: `balanceDelta` adds up the roles an account plays, so
    coinciding roles (a relayer, a self-withdrawal) are covered rather than excluded. The
    pool can't share a role (`poolIsSeparate`), as on Solana. The balances are those the
    program sees: Solana's network fee is charged before the program runs. -/
theorem balance_changes_exact
    (oldWorld newWorld : World) (inputs : TxInputs)        -- [attacker] any transaction
    (h : transact inputs oldWorld newWorld)                -- [premise] ...accepted
    (k : Pubkey) :                                         -- [premise] any account
    (newWorld.balances k : ℤ)
      = oldWorld.balances k + balanceDelta inputs oldWorld.state.pool oldWorld.nullifierRent k :=
  LeanSpec.balance_changes_exact oldWorld newWorld inputs h k

/-! ## G5. Config immutability -/

/-- **G5. Transactions can't change the pool's configuration.**
    Guards against: a transaction changing the fee rates, deposit limit, authority or rent
    reserve.

    How it is stated: every world reached by a `Run` has the config and rent-exempt minimum
    the pool was initialized with.

    Why this is the right statement: it says exactly that no transaction changes them. It
    says nothing about the authority-only config update instructions, which are not
    modeled. -/
theorem config_constant
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params)) :                         -- [attacker] any history
    ∀ j ≤ r.txs.length,
      (r.ws j).state.config = params.cfg ∧ (r.ws j).rentExemptMin = params.rentExemptMin :=
  LeanSpec.config_constant params r

end LeanSpec.Goals

/-! ## Non-vacuity: the hypotheses can hold

Read these statements: vacuity (hypotheses that can never hold together) is the main way a
theorem can say nothing. In a toy model of the hash functions (`toyHashes`, `toySha` in
`Spec/NonVacuity.lean`), and given Groth16 completeness, the hypotheses of G1a–G1d and of
G3a can all hold. Until the group types are parameters (the first step of the Groth16 verifier
bridge), this depends on Groth16 completeness being satisfiable for the abstract groups and
pairing: `Groth16Complete` is a hypothesis of each statement below, not proved. -/
namespace LeanSpec.Goals.NonVacuous
open LeanSpec

variable [Groups] [AddCommGroup G1] [Module F G1] [AddCommGroup G2] [Module F G2] [CommGroup GT]
variable [Pairing] [Deployment]

attribute [local instance] NonVacuity.toyHashes NonVacuity.toySha

/-- A run of two transactions (a deposit, then a withdrawal of that note) with witnesses
    for both proofs, where the second spends a real (non-zero) note: the hypotheses of
    G1a–G1d hold for a real spend. -/
theorem nonvacuous_spend (hCompl : Groth16Complete) :
    ∃ (r : Run NonVacuity.toyInit) (wit : ℕ → Witness),
      r.txs.length = 2 ∧ r.WitnessesFor wit ∧ (wit 1).inAmt 0 ≠ 0 :=
  NonVacuity.run_with_spend_exists hCompl

/-- The hypotheses of G3a can all hold together, for a real spend: after a one-deposit run,
    withdrawing the deposit's note (input 0 has a non-zero amount) satisfies every hypothesis
    of G3a. -/
theorem nonvacuous_G3a_hypotheses (hCompl : Groth16Complete) :
    ∃ (inputs : TxInputs) (witness : Witness) (k : ℕ),
      witness.inAmt 0 ≠ 0
      ∧ (NonVacuity.toyRun1 hCompl).WitnessesFor (fun _ => NonVacuity.toyWitness)
      ∧ RootInWindow (NonVacuity.toyRun1 hCompl) inputs.R k
      ∧ OwnsUnspentNotes (NonVacuity.toyRun1 hCompl) (fun _ => NonVacuity.toyWitness) witness k
      ∧ BuiltHonestly (NonVacuity.toyRun1 hCompl).final inputs witness
      ∧ PolicyChecksPass (NonVacuity.toyRun1 hCompl).final inputs :=
  NonVacuity.toy_G3a_hypotheses hCompl

/-- G3a's good outcome happens: after the same run, the program accepts that withdrawal. -/
theorem nonvacuous_withdrawal_accepted (hCompl : Groth16Complete) :
    CanBeAccepted (NonVacuity.wdInputs ⟨0, 0, 0⟩) (NonVacuity.toyRun1 hCompl).final :=
  NonVacuity.toy_withdrawal_accepted hCompl

end LeanSpec.Goals.NonVacuous
