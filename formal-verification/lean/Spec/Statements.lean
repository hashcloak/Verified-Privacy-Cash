import Spec.NonVacuity

/-! # Privacy Cash: security goals and theorem statements

The security properties of Privacy Cash, such as "no note is spent twice" and "every unspent
note is backed by SOL in the pool". They form five goals, G1 Balance to G5 Config authority,
each a set of theorems about the protocol model in `Spec/Spec.lean`, resting on the trusted
assumptions T0–T3.

Only the statements are here; each proof is one line pointing into `Spec/Proofs.lean`. Lean
checks that what is stated is what was proved, so the proofs need not be read.

## Trusted assumptions

T0 Deployment.
   - The trusted setup was honest: `Deployment.vk` has no known trapdoor and is the key the
     program uses. Groth16 is complete for it (`Groth16Complete`).
   - The circom circuit enforces exactly `RelationS`.
   - Nobody can replace the program.
   - The pool started from `initWorld`.
   - The Solana runtime is as modelled: transactions are atomic, instructions conserve
     lamports, and the per-slot nullifier accounts form one nullifier set.
T1 Groth16 extraction. Every verifying proof in a run comes with a witness
   (`r.WitnessesFor wit`): the honest user's own, or one extracted from the attacker who
   made it, even after the attacker has seen honest proofs (weak simulation
   extractability, for all proofs of the run).
T2 Hashes. Nobody can find a collision of `H1`–`H4`, an `H2` or `H4` preimage of `0`, or two
   byte strings whose `sha256` digests are equal mod `p` (`Sha256Collision`).
T3 Keys. Secret keys are uniform and kept secret, and `H1 sk` together with the nullifiers
   (through `signature = H3 sk c idx`) reveal nothing usable about `sk`.

## Desired Security Properties

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
  G3 Liveness                   additional: funds must not get stuck            G3a G3b G3c
  G4 Correct public payouts     docs: amount integrity                          G4a G4b
  G5 Config authority           additional                                      G5
  -  Privacy                    [ZC] Ledger indistinguishability; docs          out of scope

## The goals

G1a–G1d, G2a, G2b, G3a and G3b hold unless a hash break occurs (see "How the theorems are
stated").

**G1 Balance.** No value is created or stolen.
- G1a: a note can be spent only if it exists, belongs to the spender, and only for the
  amount it holds.
- G1b: no note is spent twice.
- G1c: the pool's SOL always backs every unspent note, exactly.
- G1d: only the owner's secret key can spend a note.
- G1e: a transaction is accepted only with a proof that verifies.

**G2 Non-malleability.** Someone who sees a transaction can't turn it to their advantage.
- G2a: they can't change its payout (recipient, amounts, fee, fee recipient, token,
  encrypted outputs). They *can* change the signer: this is intended, for relayers.
- G2b: they can't spend the same note in a different transaction without the owner's
  secret key.

**G3 Liveness.** Funds don't get stuck.
- G3a: an honest owner's spend is accepted, unless a policy check or a limit (root
  window, tree capacity) blocks it.
- G3b: nobody else can block an owner's unspent note.
- G3c (a finding, not a guarantee): once the tree is full, the pool freezes and every
  unspent note is locked for good.

**G4 Correct public payouts.** Public SOL moves exactly as the transaction says.
- G4a: no SOL is created or lost, except the rent for the two nullifier accounts.
- G4b: each account gains or pays exactly what the transaction's amount and fee say;
  no other account is touched.

**G5 Config authority.** Only the authorities change the pool's configuration.
- Transactions never change it; between transactions only signed admin changes do.
- The authorities are whoever initialized the pool (the deployment's admin, when it has
  one).

Each theorem's title and explanation are in its docstring. Each goal the code connection
carries over is a named property (end of `Spec/Vocabulary.lean`; for G1e, `proofValid`),
which the connection states of the code.

## How to read

1. This file: the goals, the trusted assumptions, each statement and its docstring.
2. The definitions they use: `Spec/Vocabulary.lean` (runs, notes, breaks, the pieces of
   G3a) and `Spec/Spec.lean` (state, `transact` and its preconditions, `initWorld`).
3. The non-vacuity statements at the end: the hypotheses can hold.
4. `Spec/Axioms.lean`: the build fails if any theorem uses `sorry` or an extra axiom.

## How the theorems are stated

**Holds or break.** Cryptography states security as "no efficient attacker can make the
property fail, except with negligible probability". Lean has no notion of efficiency,
so each theorem here says instead:

    in every history:   the property holds   OR   a hash break occurs at values from it

A hash break is concrete: e.g. two different inputs, both computed from the history's
transactions, with the same `H3` hash (`H3Collision a b`). So whoever makes the property
fail has thereby found a hash collision. That is infeasible (T2), so making the property
fail is infeasible too. The values must come from the history: "some two inputs have the
same hash" is always true (a hash compresses) and would make the theorem say nothing.

The breaks are `H1Collision`, `H2Collision` (via `PathCollision`), `H2ZeroPreimage`,
`H3Collision`, `H4Collision`, `H4ZeroPreimage` and `Sha256Collision`. G1a–G1d, G2a, G2b,
G3a and G3b end in one; their titles mean "..., unless a hash break occurs". G1e, G3c, G4a,
G4b and G5 need none: they hold outright.

**Histories (`r : Run (initWorld params)`).** Everything that happened to the pool since it
was initialized:

    ws 0 ─between 0─▶ · ─txs[0]─▶ ws 1 ─between 1─▶ · ─txs[1]─▶ ws 2  ···  ws n = r.final
                              │                             │
                            wit 0                         wit 1

- `ws 0 = initWorld params`: the freshly initialized pool.
- `txs[j]`: the `j`-th transaction the program accepted (`transact`).
- `between j`: what happened outside the program before it, limited to what Solana allows
  (`Between.Allowed`): SOL sent to any account, other accounts spending, config changes
  signed by the right authority.
- `ws j`: the world (pool state, balances, config) before `between j`.
Every world the pool can reach is the end of some history (`ReachableWorld.exists_run`),
so stating the theorems over histories misses nothing.

**Witnesses (`wit`).** The chain sees a transaction's public inputs and proof only. The
secrets behind it (the spent notes, their owners' keys, the amounts) are its witness
`wit j`, and properties such as "the spent note exists" are about them. A theorem takes any
`wit` with `r.WitnessesFor wit`: for each transaction whose proof verifies, `wit j`
satisfies the circuit (`RelationS`). The theorems hold for every such `wit`.
Assuming T1, whoever made transaction `j` knows `wit j`. So when a theorem says
`wit j` contains the owner's secret key, whoever made transaction `j` knows that key.

## Where each hypothesis comes from

A theorem is only as strong as the reasons its hypotheses hold. So every hypothesis of
every theorem is tagged with why it is fair to assume:
- `[attacker]`: the attacker chooses it. The theorem holds for every choice, so this
  makes the theorem stronger, not weaker.
- `[owner]`: the honest owner makes it true by following the protocol. Fair to assume,
  because the guarantee is for that owner.
- `[premise]`: the situation the theorem is about (e.g. "this note is unspent"). It
  scopes the claim.
- `[policy]`: a program policy check (e.g. the deposit limit). It may block a
  transaction; that is intended.
- `[limit]`: a protocol limit (root window, tree capacity, `u64` balances). It may block
  a transaction; that is intended.
- `[trust Tn]`: a trusted assumption, not proved; see below.

No hypothesis states a fact about the state that an attacker could make false (e.g. "the
nullifier is unused"): such facts are proved instead. Otherwise an attacker could make the
hypothesis false and the theorem would say nothing.

## Out of scope

  - Privacy: a probabilistic property (an indistinguishability game), which this model
    can't express. It also depends on the anonymity set: deposits and withdrawals are
    public.
  - SPL tokens: SOL only. The circuit does not link `mint` to `mintAddr`, so for SPL tokens
    asset separation must come from per-mint trees and the global nullifier set.
  - Solana network fees: charged before the program runs; `balances` are what the program
    sees.

## Limitations

  - **A spend must use a recent root.** The tree keeps its last 100 roots, and each
    transaction adds two (one per output note), so a root expires after about 50
    transactions. G3a only covers spends whose root has not expired; an owner whose
    proof is built on an expired root must rebuild it against a newer one (finding F7).

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
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    SpendsAreGenuine r wit :=
  fun j hj i hne => LeanSpec.spends_are_genuine params r wit hwit j hj i hne

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
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    NoDoubleSpend r wit :=
  fun j hj j' hj' i i' hne hne' hdiff hsame =>
    LeanSpec.no_double_spend params r wit hwit j j' hj hj' i i' hne hne' hdiff hsame

/-- **G1c. Every unspent note is fully backed by SOL in the pool.**
    Guards against: value created from nothing (inflation), which would leave the pool
    unable to pay out all notes; and SOL disappearing from the pool.

    How it is stated: in any `Run`, the pool's SOL equals its rent reserve plus the total
    value of the notes not yet spent plus the SOL sent to the pool from outside during the run
    (`r.donated`), or a hash break of G1a/G1b occurs (`BalanceBreak`). A note's value comes
    from the witness of the transaction that created it; "not yet spent" means no non-zero
    input opened its leaf.

    Why this is the right statement: inflation is private value exceeding the SOL that
    backs it, so the two are compared directly. An equality rules out both directions.
    Anyone can send SOL to the pool between transactions (`Between.Allowed`), so the pool can
    hold more than its notes; that SOL is counted exactly rather than stating `≥`, which
    would hide SOL leaking out of the pool while outside SOL covers it. -/
theorem balance
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    PoolBacksNotes params r wit :=
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
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    OnlyOwnerSpends r wit :=
  fun j hj i hne skOwner hOwner =>
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
    (h : transact inputs oldWorld newWorld) :              -- [premise] ...accepted
    proofValid inputs :=
  Classical.byContradiction fun hn => LeanSpec.transact_requires_valid_proof oldWorld newWorld inputs hn h

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
    determines every field. A proof for *new* public inputs is G2b.

    Not covered: the signer `s`, which is not bound. Replacing it only changes who pays the
    deposit and the rent for the two nullifier accounts; the notes, recipient and amounts
    stay as the honest owner chose. This is intended: it lets relayers submit transactions. -/
theorem same_public_inputs_same_external_data
    (T' : TxInputs) (oldWorld' newWorld' : World)          -- [attacker] the attacker's transaction
    (h' : transact T' oldWorld' newWorld') :               -- [attacker] ...accepted
    ∀ T, CopiedProofSamePayout T T' :=                     -- [premise] any honest transaction seen
  fun T hT hSame => LeanSpec.same_public_inputs_same_external_data T T' oldWorld' newWorld' hT h' hSame

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
    capacity (G3c). -/
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
    (r : Run (initWorld params)) :                         -- [attacker] any history
    FullTreeFreezes r :=
  fun hfull b inputs new => LeanSpec.full_tree_freezes_pool params r hfull b inputs new

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
    NoSolCreated inputs oldWorld newWorld :=
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
    (h : transact inputs oldWorld newWorld) :              -- [premise] ...accepted
    ExactPayouts inputs oldWorld newWorld :=
  fun k => LeanSpec.balance_changes_exact oldWorld newWorld inputs h k

/-! ## G5. Config authority -/

/-- **G5. Only the authorities change the pool's configuration.**
    Guards against: a transaction or an outsider changing the fee settings, the deposit
    limit, the authorities or the rent reserve; an error margin above 100%; and anyone but
    the deployment's admin taking control of the configuration.

    How it is stated: every world reached by a `Run` has a config reached from the initial
    one by allowed admin changes (`AdminChanges`: new fee settings signed by the config's
    authority, a new deposit limit signed by the limit authority), both authorities are
    whoever initialized the pool (the deployment's admin, when it has one:
    `InitParams.admin_init`), the error margin is at most 10000 basis points, and the
    rent-exempt minimum is the initial one.

    Why this is the right statement: transactions don't change the config at all, and between
    transactions only allowed admin changes do. -/
theorem config_changes_only_by_authority
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params)) :                         -- [attacker] any history
    ConfigOnlyByAuthority params r :=
  LeanSpec.config_changes_only_by_authority params r

end LeanSpec.Goals

/-! ## Non-vacuity: the hypotheses can hold

Vacuity (hypotheses that can never hold together) is the main way a theorem can say
nothing. In a toy model (`Spec/NonVacuity.lean`), the hypotheses of G1a–G1d
and of G3a can all hold, and G3a's good outcome happens. The toy model is deliberately broken:
the hash functions (`toyHashes`, `toySha`) and the groups and pairing (`toyGroups`,
`toyPairing`: `G1 = G2 = F`, `GT = Unit`, every pairing is `1`, every byte string decodes, the
key is all zeros) are not cryptographic. With that pairing every proof verifies, so Groth16
completeness, a hypothesis of G3a, is proved (`toyComplete`) rather than assumed. So these
statements show the hypotheses can hold together, not that real cryptography reaches the good
outcome. -/
namespace LeanSpec.Goals.NonVacuous
open LeanSpec

attribute [local instance] NonVacuity.toyHashes NonVacuity.toySha NonVacuity.toyGroups
  NonVacuity.toyG1Group NonVacuity.toyG2Group NonVacuity.toyG1Module NonVacuity.toyG2Module
  NonVacuity.toyGTGroup NonVacuity.toyPairing NonVacuity.toyDeployment

/-- A run of two transactions (a deposit, then a withdrawal of that note) with witnesses
    for both proofs, where the second spends a real (non-zero) note: the hypotheses of
    G1a–G1d hold for a real spend. Toy hashes and a toy pairing. -/
theorem nonvacuous_spend :
    ∃ (r : Run NonVacuity.toyInit) (wit : ℕ → Witness),
      r.txs.length = 2 ∧ r.WitnessesFor wit ∧ (wit 1).inAmt 0 ≠ 0 :=
  NonVacuity.run_with_spend_exists NonVacuity.toyComplete

/-- The hypotheses of G3a can all hold together, for a real spend: after a one-deposit run,
    withdrawing the deposit's note (input 0 has a non-zero amount) satisfies every hypothesis
    of G3a. Groth16 completeness holds in the toy model (`toyComplete`). -/
theorem nonvacuous_G3a_hypotheses :
    Groth16Complete ∧
    ∃ (inputs : TxInputs) (witness : Witness) (k : ℕ),
      witness.inAmt 0 ≠ 0
      ∧ (NonVacuity.toyRun1 NonVacuity.toyComplete).WitnessesFor (fun _ => NonVacuity.toyWitness)
      ∧ RootInWindow (NonVacuity.toyRun1 NonVacuity.toyComplete) inputs.R k
      ∧ OwnsUnspentNotes (NonVacuity.toyRun1 NonVacuity.toyComplete)
          (fun _ => NonVacuity.toyWitness) witness k
      ∧ BuiltHonestly (NonVacuity.toyRun1 NonVacuity.toyComplete).final inputs witness
      ∧ PolicyChecksPass (NonVacuity.toyRun1 NonVacuity.toyComplete).final inputs :=
  ⟨NonVacuity.toyComplete, NonVacuity.toy_G3a_hypotheses NonVacuity.toyComplete⟩

/-- G3a's good outcome happens: after the same run, the program accepts that withdrawal.
    Toy hashes and a toy pairing: it shows the outcome is reachable, not that real
    cryptography reaches it. -/
theorem nonvacuous_withdrawal_accepted :
    CanBeAccepted (NonVacuity.wdInputs ⟨[], [], []⟩)
      (NonVacuity.toyRun1 NonVacuity.toyComplete).final :=
  NonVacuity.toy_withdrawal_accepted NonVacuity.toyComplete

end LeanSpec.Goals.NonVacuous
