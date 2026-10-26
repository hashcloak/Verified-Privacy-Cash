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
T1 Groth16 extraction; proofs show knowledge. Whoever makes a proof that verifies knows a
   witness for it.
T2 Hashes. Nobody can find a collision of `H1`–`H4`, an `H2` or `H4` preimage of `0`, or
   two byte strings whose `sha256` digests are equal mod `p` (`Sha256Collision`).
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
  G1 Balance                    [ZC] Balance; docs: double-spend prevention,    G1a–G1d
                                amount integrity
  G2 Non-malleability           [ZC] Transaction non-malleability               G2a G2b
  G3 Liveness                   additional: funds must not get stuck            G3a G3b G3c
  G4 Correct public payouts     docs: amount integrity                          G4a G4b
  G5 Config authority           additional                                      G5
  -  Privacy                    [ZC] Ledger indistinguishability; docs          out of scope

## The goals

**G1 Balance.** No value is created or stolen.
- G1a: a note can be spent only if it exists, belongs to the spender, and only for the
  amount it holds.
- G1b: no note is spent twice.
- G1c: no inflation: the pool's SOL always backs every unspent note, exactly.
- G1d: only the owner's secret key can spend a note.

**G2 Non-malleability.** Someone who sees a transaction can't turn it to their advantage.
- G2a: they can't change its payout (recipient, amounts, fee, fee recipient, token,
  encrypted outputs). They *can* change the signer: this is intended, for relayers.
- G2b: they can't reveal its note's nullifier in a transaction of their own (front-running
  it) without the owner's secret key.

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
carries over is a named property, defined just above its theorem,
which the connection states of the code.

## How to read

1. This file: the goals, the trusted assumptions, and for each goal its property and theorem.
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
G3a and G3b end in one; their titles mean "..., unless a hash break occurs". G3c, G4a, G4b
and G5 need none: they hold outright.

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
satisfies the circuit (`RelationS`). Every accepted transaction's proof verifies (`transact`
requires it, `validZKP`), so this gives a witness for every transaction of the run. The
theorems hold for every such `wit`. Assuming T1, whoever made transaction `j` knows `wit j`.
So when a theorem says `wit j` contains the owner's secret key, whoever made transaction `j`
knows that key.

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

/-! ### G1a. Spends are genuine

In every run, every spend (non-zero input) is of a real note, unless a hash break occurs
(`HashBreakInSpend`):
- **the note exists:** it is at a tree leaf created by an earlier transaction;
- **the spender holds its key:** the spender's secret key hashes to the note's owner public
  key (by T1, the spender knows that key);
- **the value is real:** the spent amount (and token) is the one the note was created with.

Guards against: spending a made-up note, someone else's note, or a real note for more than
it holds. -/

/-- The property G1a proves: `SpendsAreGenuine r wit`: every spend in run `r` is of a real
    note (it exists, the spender holds its key, the value is real), or a hash break occurs.

    For each non-zero input `i` of each transaction `j`, either:
    - **genuine:** it opens a leaf created by an earlier transaction (`< 2j`), and the
      spent note equals the note stored there; or
    - **a hash break** (`HashBreakInSpend`) occurs. -/
def SpendsAreGenuine {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  -- For all txs, for both input amounts when they are an actual spend (not 0):
  ∀ j < r.txs.length, ∀ i : Fin 2, (wit j).inAmt i ≠ 0 →
    -- Either the note already existed:
    -- (Part 1) The position it opens is in the first 2j leaves of the tree (which are the ones created by txs 0,..,j-1)
    -- (Part 2) Check that the note the txs spends equals the earlier leaf created at that position
    (openedPos wit j i < 2 * j ∧ (wit j).inNote i = leafNote wit (openedPos wit j i))
    -- Or there's a break with hash assumptions (T2)
    ∨ HashBreakInSpend r wit j i

/-- **G1a.** `SpendsAreGenuine` holds in every run from a freshly initialized pool.

Why this is the right statement: each of the three attacks makes the spent note differ from
the stored one. The stored note is taken from the accepted transactions themselves, not
chosen freely. -/
theorem spends_are_genuine
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    SpendsAreGenuine r wit :=
  fun j hj i hne => LeanSpec.spends_are_genuine params r wit hwit j hj i hne

/-! ### G1b. No note is spent twice

In every run, no note is spent twice, unless a hash break occurs.

Guards against: spending the same note again, in a later transaction or twice within one
transaction. -/

/-- The property G1b proves: `NoDoubleSpend r wit`: no note is spent twice in run `r`, or a
    hash break occurs.

    If two different non-zero inputs `(j, i) ≠ (j', i')` open the same leaf,
    then one of these hash breaks occurs:
    - **a forged spend:** one of the two spends is not genuine (`HashBreakInSpend`, the
      failure case of G1a);
    - **two secret keys for the same public key:** the two spends use different secret keys
      with the same public key (`H1Collision`). -/
def NoDoubleSpend {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  -- For any two inputs in the run that spend the same note,
  ∀ j < r.txs.length, ∀ j' < r.txs.length, ∀ i i' : Fin 2, DoubleSpend wit j i j' i' →
    -- a hash break occurs
    HashBreakInSpend r wit j i ∨ HashBreakInSpend r wit j' i' ∨ H1Collision ((wit j).inSk i) ((wit j').inSk i')

/-- **G1b.** `NoDoubleSpend` holds in every run from a freshly initialized pool.

Why this is the right statement: by G1a every spend opens the leaf holding exactly the note
it spends, so "a note is spent twice" means "two inputs open the same leaf". The two inputs
are any pair in the run, so both later and same-transaction re-spends are covered. -/
theorem no_double_spend
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    NoDoubleSpend r wit :=
  fun j hj j' hj' i i' ⟨hdiff, hne, hne', hsame⟩ =>
    LeanSpec.no_double_spend params r wit hwit j j' hj hj' i i' hne hne' hdiff hsame

/-! ### G1c. No inflation: the pool's SOL exactly backs the unspent notes

No value is created or lost inside the pool: in every run, the unspent notes are worth
exactly the SOL the pool holds for them, unless a hash break of G1a or G1b occurs.

Precisely, at the end of every run:

    pool SOL  =  value of the unspent notes  +  initial rent reserve  +  donations

The three terms count different SOL, each once:
- **value of the unspent notes:** the SOL deposits brought in (through `transact`), minus
  what withdrawals and fees paid out;
- **initial rent reserve** (`rentExemptMin`): the SOL the pool was created with at
  `initialize`, the minimum it must keep so Solana doesn't delete its account. It is
  never paid out: a withdrawal is accepted only if the pool keeps at least this much
  (`poolSolvent`);
- **donations** (`r.donated`): SOL sent straight to the pool's address between
  transactions, outside the program. No note is created for it, so no one can withdraw it.

Guards against:
- **inflation:** notes worth more than the SOL that backs them, so the pool can't pay out
  all notes;
- **leaks:** SOL disappearing from the pool. -/

/-- The property G1c proves: `PoolBacksNotes params r wit`: at the end of run `r`, the
    pool's SOL exactly backs the unspent notes, or a hash break occurs.

    Either:
    - **backed:** pool SOL = value of the unspent notes + initial rent reserve + donations
      (`r.donated`: SOL sent straight to the pool, outside `transact`); or
    - **a hash break** (`BreakInSomeSpend`) occurs. -/
def PoolBacksNotes (params : InitParams) (r : Run (initWorld params)) (wit : ℕ → Witness) : Prop :=
  (r.final.poolBalance : ℤ) = params.rentExemptMin + ∑ pos ∈ r.unspent wit, leafValue wit pos + r.donated
  ∨ BreakInSomeSpend r wit

/-- **G1c.** `PoolBacksNotes` holds in every run from a freshly initialized pool.

Why this is the right statement:
- **notes vs. SOL, directly:** inflation means the notes are worth more than the SOL behind
  them, so the statement compares exactly those two.
- **an equality, not `≥`:** it rules out both inflation and leaks. With `≥`, donations
  could hide SOL leaking out of the pool; counting them exactly closes that gap. -/
theorem balance
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    PoolBacksNotes params r wit :=
  LeanSpec.balance params r wit hwit

/-! ### G1d. Only the owner's secret key can spend a note

In every run, a spend of a note uses the note owner's secret key, unless a hash break
occurs.-/

/-- The property G1d proves: `OnlyOwnerSpends r wit`: every spend in run `r` uses the
    owner's secret key, or a hash break occurs.

    If a non-zero input spends a note whose owner public key is `H1 skOwner`,
    then either:
    - **the owner's key:** the input's secret key is `skOwner`; or
    - **a hash break:** a `HashBreakInSpend` occurs, or `skOwner` and the input's key
      collide under `H1`. -/
def OnlyOwnerSpends {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  ∀ j < r.txs.length, ∀ i : Fin 2, ∀ skOwner,
    -- if it is a real spend (input amount not 0)
    (wit j).inAmt i ≠ 0
    -- of a note owned by `H1 skOwner`,
    ∧ (leafNote wit (openedPos wit j i)).ownerPk = H1 skOwner →
    (wit j).inSk i = skOwner ∨ HashBreakInSpend r wit j i ∨ H1Collision skOwner ((wit j).inSk i)

/-- **G1d.** `OnlyOwnerSpends` holds in every run from a freshly initialized pool.-/
theorem honest_note_spent_only_with_owner_key
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [trust T1] the witnesses of its proofs
    OnlyOwnerSpends r wit :=
  fun j hj i skOwner ⟨hne, hOwner⟩ =>
    LeanSpec.honest_note_spent_only_with_owner_key params r wit hwit j hj i hne skOwner hOwner

/-! ## G2. Non-malleability -/

/-! ### G2a. A copied proof can't redirect the payout

An attacker who copies an honest transaction's proof can change only its signer: everything
else is fixed by the proof's public inputs, unless `sha256` collides on the external data.
The honest transaction has been seen (e.g. broadcast) but not yet accepted: the attacker's
copy is accepted instead, and the honest one then fails, since they share nullifiers.

Guards against: an attacker who sees an honest transaction, reuses (or re-randomizes) its
proof, and changes the recipient, amount, fee, fee recipient, encrypted outputs or token.

Not covered: the signer `s`, which is not bound. Replacing it only changes who pays the
deposit and the rent for the two nullifier accounts; the notes, recipient and amounts stay
as the honest owner chose. This is intended: it lets relayers submit transactions. -/

/-- `ExtDataWellFormed T`: the honest transaction `T`, as observed, is well formed: its
    external data hashes to the value its proof commits to (`externalDataBound`), and its
    amounts and encrypted outputs are in range (`amountsInRange`, `encOutsFit`), so that
    the serialized external data determines every field.
    These checks are needed since the txs has not been processed, only submitted.
    -/
def ExtDataWellFormed (T : TxInputs) : Prop :=
  externalDataBound T ∧ amountsInRange T.extAmt T.f ∧ encOutsFit T

/-- The property G2a proves: `SamePayout T T'`: the transactions `T` and `T'` pay out the
    same, or `sha256` collides.

    Either:
    - **same payout:** `T` and `T'` have the same recipient, amount, encrypted outputs,
      fee, fee recipient and token; or
    - **a hash break** (`Sha256Collision`): `sha256` collides on their serialized external
      data. -/
def SamePayout (T T' : TxInputs) : Prop :=
  -- Either the same payout (only the signer may differ, not the beneficiaries)
  -- (this covers the fields of `TxInputs` that are not public inputs)
  (T.A = T'.A ∧ T.extAmt = T'.extAmt ∧ T.encOut0 = T'.encOut0 ∧ T.encOut1 = T'.encOut1
    ∧ T.f = T'.f ∧ T.t = T'.t ∧ T.mintAddr = T'.mintAddr)
  -- or a sha256 collision occurred
  ∨ Sha256Collision (serealizeExternalData T) (serealizeExternalData T')

/-- **G2a.** If an attacker's accepted transaction has an honest transaction's public
    inputs, the two pay out the same (`SamePayout`).

    Why this is the right statement: copying or re-randomizing a proof needs no secrets but
    keeps its public inputs, which include the hash of the external data, which fixes all
    fields. -/
theorem same_public_inputs_same_external_data
    (T : TxInputs)                                         -- [premise] an honest transaction, seen
                                                           --   but not yet accepted
    (hT : ExtDataWellFormed T)                             -- [premise] ...well formed
    (T' : TxInputs) (oldWorld' newWorld' : World)          -- [attacker] the attacker's transaction,
                                                           --   and the pool before and after it
    (hSame : T.pubInputs = T'.pubInputs)                   -- [attacker] ...with the honest one's
                                                           --   public inputs
    (h' : transact T' oldWorld' newWorld') :               -- [premise] if the program accepted it
    -- Then, the same payout must happen (the only thing to change is the signer)
    SamePayout T T' :=
  LeanSpec.same_public_inputs_same_external_data T T' oldWorld' newWorld' hT h' hSame

/-! ### G2b. Revealing a note's nullifier requires the owner's key

Revealing the same nullifier as an honest transaction requires the note owner's secret key,
unless a hash collision occurs.

Relation to G1d: this is the [ZC] form of G1d. G1d is about real spends in a run, by tree
position; G2b is about nullifiers, for any two circuit witnesses, with no run or tree. So it
also covers a zero-amount ("dummy") input that reveals the honest note's nullifier.

How it is stated: if two witnesses (each satisfying the circuit) reveal the same nullifier,
they contain the same secret key, unless `H3`, `H4` or `H1` collide on values from the two
witnesses. -/

/-- **G2b.** Two witnesses that reveal the same nullifier hold the same secret key, or a
    hash collision occurs. -/
theorem shared_nullifier_requires_owner_key
    (x : PubInputs) (w : Witness) (hRel : RelationS x w)   -- [premise] the honest transaction's
                                                           --   statement and its owner's witness
    (x' : PubInputs) (w' : Witness)                        -- [attacker] the attacker's statement
    (hRel' : RelationS x' w')                              -- [assumption T1] ...witness from attacker
    (i i' : Fin 2)                                         -- [premise] an input of each
    (hShared : x.nullifiers i = x'.nullifiers i') :        -- [premise] if they reveal the same nullifier
    -- They must have used the same secret key
    w'.inSk i' = w.inSk i
    -- Or a break has happened
    ∨ NullifierCollision w i w' i'
    ∨ H1Collision (w.inSk i) (w'.inSk i') :=
  (LeanSpec.shared_nullifier_requires_owner_key x x' w w' hRel hRel' i i' hShared).imp_right
    or_assoc.mpr

/-! ## G3. Liveness -/

/-! ### G3a. An honest owner's spend is accepted

An honest owner's spend is accepted, unless a policy check or a limit blocks it, or an
attacker-side hash break occurs.

Guards against: funds getting stuck because the program rejects an honest owner: on the
proof, the root, the Merkle path, an already-used nullifier, or pool solvency.

How it is stated: after any `Run`, when an honest owner tries to spends notes it owns
( notes are unspent (`OwnsUnspentNotes`), root is in history (`RootInWindow`), with a
transaction built honestly (`BuiltHonestly`)), then:
- If the policy checks pass (`PolicyChecksPass`), the program accepts the transaction (`CanBeAccepted`),
- OR an attacker-side hash break occurs (`SpendBlockedByBreak`).-/

/-- **G3a.** An honest owner's spend is accepted, or an attacker-side hash break occurs. -/
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
    CanBeAccepted inputs r.final ∨ SpendBlockedByBreak r wit witness k :=
  LeanSpec.unspent_note_is_spendable params hCompl r wit hwit inputs witness k hRoot hNotes
    hHonest hPolicy

/-! ### G3b. Nobody can block an unspent note

The nullifier of an unspent note is not yet used, unless a hash collision occurs.

Guards against: an attacker making an owner's note unspendable by using up its nullifier
first, e.g. with a zero-amount ("dummy") input, which needs no Merkle path.

How it is stated: for any `Run`, any witnesses `wit`, and any note with non-zero amount that
no spend of the run has opened (`pos ∈ r.unspent wit`), the note's nullifier is not yet in
the nullifier set, unless an `H3` or `H4` collision occurs (`NullifierTaken`).

Why this is the right statement: blocking a note means its nullifier is spent while the note
itself was never spent. Equal nullifiers mean equal commitment, position and signature (or
an `H3` collision), and an equal commitment means an equal note, amount included (or an
`H4` collision). So the other input would be a non-zero spend of the same note at the same
position, which `pos ∈ r.unspent wit` excludes. Binding the position into the nullifier is
what defeats the "Faerie Gold" attack (Zcash Protocol Specification §8.4). -/

/-- **G3b.** An unspent note's nullifier is not yet used, or a hash collision occurs. -/
theorem unspent_note_cannot_be_blocked
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)        -- [trust T1] the witnesses of its proofs
    (w : Witness) (i : Fin 2)                              -- [owner] the owner's secrets, input `i`
    (hne : w.inAmt i ≠ 0)                                  -- [premise] ...a real note
    (hpos : (w.openings i).index.val ∈ r.unspent wit) :    -- [premise] ...that is unspent
    w.inNullifier i ∉ r.final.state.nullifiers
    ∨ NullifierTaken r wit w i :=
  LeanSpec.unspent_note_cannot_be_blocked params r wit hwit w i hne hpos

/-! ### G3c. A full tree freezes the pool (a finding, not a guarantee)

Once the tree is full, no transaction is accepted, withdrawals included, and every unspent
note is locked for good.

Guards against: nothing; this records a limitation. Every transaction appends two notes, so
the tree's capacity (`2^26` leaves) is reached after `2^25` transactions.

Why this is the right statement: it shows exactly when liveness (G3a) ends. -/

/-- The property G3c proves: `FullTreeFreezes r`: once run `r` has filled the tree, no
    further transaction is accepted.

    If `r` has at least `2^25` transactions (`2^26` leaves), then whatever
    happens after its last transaction (`b`), no transaction is accepted. -/
def FullTreeFreezes {w0 : World} (r : Run w0) : Prop :=
  2^25 ≤ r.txs.length → ∀ (b : Between) (inputs : TxInputs) (new : World),
    ¬ transact inputs (r.final.between b) new

/-- **G3c.** `FullTreeFreezes` holds in every run from a freshly initialized pool. -/
theorem full_tree_freezes_pool
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params)) :                         -- [attacker] any history
    FullTreeFreezes r :=
  fun hfull b inputs new => LeanSpec.full_tree_freezes_pool params r hfull b inputs new

/-! ## G4. Correct public payouts -/

/-! ### G4a. No SOL is created or lost, except the nullifier rent

In every accepted transaction, the accounts it touches end with their total SOL before,
minus the rent for the two new nullifier accounts.

Guards against: a transaction that changes the total SOL held by the pool and the accounts
it touches, other than by the rent for the two new nullifier accounts.

Why this is the right statement: conservation is about totals, so it is stated over every
account the transaction touches at once, whatever roles coincide. The pool is an ordinary
account here, as on Solana. The rent goes to the two new nullifier accounts, which are not
tracked in `balances`. Every other account is unchanged (G4b). -/

/-- The property G4a proves: `NoSolCreated inputs old new`: the transaction from `old` to
    `new` creates and loses no SOL, except the nullifier rent.

    The pool, the signer, the recipient and the fee recipient (each counted
    once, even if roles coincide) together end with their total before, minus twice the
    nullifier rent. -/
def NoSolCreated (inputs : TxInputs) (old new : World) : Prop :=
  ∑ k ∈ ({inputs.s, inputs.A, inputs.t, old.state.pool} : Finset Pubkey), (new.balances k : ℤ)
  = ∑ k ∈ ({inputs.s, inputs.A, inputs.t, old.state.pool} : Finset Pubkey), (old.balances k : ℤ)
    - 2 * old.nullifierRent

/-- **G4a.** `NoSolCreated` holds for every accepted transaction. -/
theorem no_sol_created
    (oldWorld newWorld : World) (inputs : TxInputs)        -- [attacker] any transaction, and the
                                                           --   pool before and after it
    (h : transact inputs oldWorld newWorld) :              -- [premise] the program accepted it
    NoSolCreated inputs oldWorld newWorld :=
  LeanSpec.no_sol_created oldWorld newWorld inputs h

/-! ### G4b. Every account gets exactly what it is owed and pays exactly what it owes

In every accepted transaction, each account's SOL changes by exactly what the transaction's
amount and fee say, and no other account is touched.

Guards against: the recipient or fee recipient being paid the wrong amount, the signer being
charged the wrong amount (in particular a deposit the signer doesn't pay for), the pool
gaining or losing the wrong amount, and any uninvolved account being touched.

Why this is the right statement: `balanceDelta` adds up the roles an account plays
(`|extAmt|` to the recipient on a withdrawal, `f` to the fee recipient, `extAmt` and twice
the nullifier rent from the signer, `extAmt − f` to the pool), so coinciding roles (a
relayer, a self-withdrawal) are covered rather than excluded. The pool can't share a role
(`poolIsSeparate`), as on Solana. The balances are those the program sees: Solana's network
fee is charged before the program runs. -/

/-- The property G4b proves: `ExactPayouts inputs old new`: in the transaction from `old` to
    `new`, every account changes by exactly what it is owed or owes.

    Every account `k` changes by `balanceDelta` (zero for accounts the
    transaction doesn't involve). -/
def ExactPayouts (inputs : TxInputs) (old new : World) : Prop :=
  ∀ k, (new.balances k : ℤ) = old.balances k + balanceDelta inputs old.state.pool old.nullifierRent k

/-- **G4b.** `ExactPayouts` holds for every accepted transaction. -/
theorem balance_changes_exact
    (oldWorld newWorld : World) (inputs : TxInputs)        -- [attacker] any transaction, and the
                                                           --   pool before and after it
    (h : transact inputs oldWorld newWorld) :              -- [premise] the program accepted it
    ExactPayouts inputs oldWorld newWorld :=
  fun k => LeanSpec.balance_changes_exact oldWorld newWorld inputs h k

/-! ## G5. Config authority -/

/-! ### G5. Only the authorities change the pool's configuration

In every run, only the authorities have changed the configuration, and the authorities are
whoever initialized the pool (the deployment's admin, when it has one).

Guards against: a transaction or an outsider changing the fee settings, the deposit limit,
the authorities or the rent reserve; an error margin above 100%; and anyone but the
deployment's admin taking control of the configuration.

Why this is the right statement: transactions don't change the config at all, and between
transactions only allowed admin changes do (`AdminChanges`: new fee settings signed by the
config's authority, a new deposit limit signed by the limit authority). The admin link is
`InitParams.admin_init`. -/

/-- The property G5 proves: `ConfigOnlyByAuthority params r`: throughout run `r`, only the
    authorities have changed the config, and the authorities are whoever initialized the
    pool.

    In every world of `r`:
    - **only allowed changes:** the config was reached from the initial one by allowed
      admin changes (`AdminChanges`);
    - **the authorities:** both are whoever initialized the pool (the deployment's admin,
      when it has one);
    - **the fee margin:** at most 10000 basis points (100%);
    - **the rent:** the rent-exempt minimum is the initial one. -/
def ConfigOnlyByAuthority (params : InitParams) (r : Run (initWorld params)) : Prop :=
  ∀ j ≤ r.txs.length,
    AdminChanges params.cfg (r.ws j).state.config ∧
    (r.ws j).state.config.authority = params.initializer ∧
    (r.ws j).state.config.limitAuthority = params.initializer ∧
    (r.ws j).state.config.feeMarginError ≤ 10000 ∧
    (r.ws j).rentExemptMin = params.rentExemptMin

/-- **G5.** `ConfigOnlyByAuthority` holds in every run from a freshly initialized pool. -/
theorem config_changes_only_by_authority
    (params : InitParams)                                  -- [premise] a freshly initialized pool
    (r : Run (initWorld params)) :                         -- [attacker] any history
    ConfigOnlyByAuthority params r :=
  LeanSpec.config_changes_only_by_authority params r

end LeanSpec.Goals

/-! ## Non-vacuity: the hypotheses can hold

Vacuity (hypotheses that can never hold together) is the main way a theorem can say
nothing. In a toy model (`Spec/NonVacuity.lean`), the hypotheses of G1a–G1d and of G3a
can all hold, and G3a's good outcome happens. The toy model is deliberately broken: the
hash functions (`toyHashes`, `toySha`) and the groups and pairing (`toyGroups`,
`toyPairing`: `G1 = G2 = F`, `GT = Unit`, every pairing is `1`, every byte string decodes,
the key is all zeros) are not cryptographic. With that pairing every proof verifies, so
Groth16 completeness, a hypothesis of G3a, is proved (`toyComplete`) rather than assumed.
So these statements show the hypotheses can hold together, not that real cryptography
reaches the good outcome. -/
namespace LeanSpec.Goals.NonVacuous
open LeanSpec

attribute [local instance] NonVacuity.toyHashes NonVacuity.toySha NonVacuity.toyGroups
  NonVacuity.toyG1Group NonVacuity.toyG2Group NonVacuity.toyG1Module NonVacuity.toyG2Module
  NonVacuity.toyGTGroup NonVacuity.toyPairing NonVacuity.toyDeployment

/-- **The hypotheses of G1a–G1d can hold, on a real spend.** A run of two transactions (a
    deposit, then a withdrawal of that note) with witnesses for both proofs, where the
    second spends a real (non-zero) note. Toy hashes and a toy pairing. -/
theorem nonvacuous_spend :
    ∃ (r : Run NonVacuity.toyInit) (wit : ℕ → Witness),
      r.txs.length = 2 ∧ r.WitnessesFor wit ∧ (wit 1).inAmt 0 ≠ 0 :=
  NonVacuity.run_with_spend_exists NonVacuity.toyComplete

/-- **The hypotheses of G3a can all hold together, on a real spend.** After a one-deposit
    run, withdrawing the deposit's note (input 0 has a non-zero amount) satisfies every
    hypothesis of G3a. Groth16 completeness holds in the toy model (`toyComplete`). -/
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

/-- **G3a's good outcome happens.** After the same run, the program accepts that
    withdrawal. Toy hashes and a toy pairing: it shows the outcome is reachable, not that
    real cryptography reaches it. -/
theorem nonvacuous_withdrawal_accepted :
    CanBeAccepted (NonVacuity.wdInputs ⟨[], [], []⟩)
      (NonVacuity.toyRun1 NonVacuity.toyComplete).final :=
  NonVacuity.toy_withdrawal_accepted NonVacuity.toyComplete

end LeanSpec.Goals.NonVacuous
