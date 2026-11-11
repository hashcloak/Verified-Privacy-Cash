import Spec.Proofs

/-! # Privacy Cash: security goals and theorem statements

The security properties of Privacy Cash, such as "no note is spent twice" and "every unspent
note is backed by SOL in the pool". They form five goals, G1 Balance to G5 Admin control,
each a set of theorems about the protocol model in `Spec/Spec.lean`, resting on the trusted
assumptions T0–T3.

Only the statements are here; each proof is one line pointing into `Spec/Proofs.lean`. Lean
checks that what is stated is what was proved, so the proofs need not be read.

## Trusted assumptions

T0 Deployment.
   - `Deployment.vk` is the key the program uses.
   - The circom circuit enforces exactly `RelationS`.
   - Nobody can replace the program.
   - The pool started from `initWorld`.
   - The Solana runtime is as modelled: transactions are atomic, instructions conserve
     lamports, and the per-slot nullifier accounts form one nullifier set.
   - Every G1 and G2 point has a byte encoding the program decodes.
T1 Groth16. For the deployed key:
   - The trusted setup was honest: nobody knows its trapdoor.
   - Completeness: every statement with a witness has a verifying proof. This is why an honest
     owner has the proof G3a takes as given (`validProof`).
   - Extraction; proofs show knowledge: whoever makes a proof that verifies knows a witness
     for it.
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
  G3 Liveness                   additional: funds must not get stuck            G3a G3b
  G4 Correct public payouts     docs: amount integrity                          G4a G4b
  G5 Admin control              additional                                      G5a G5b
  -  Privacy                    [ZC] Ledger indistinguishability; docs          out of scope

## The goals

**G1 Balance.** No value is created or stolen.
- G1a: a note can be spent only if it exists, belongs to the spender, and only for the
  amount it holds.
- G1b: no note is spent twice, across transactions or within one.
- G1c: no inflation: the pool's SOL always backs every unspent note, exactly.
- G1d: only the owner's secret key can spend a note.

**G2 Non-malleability.** Someone who sees a transaction can't turn it to their advantage.
- G2a: they can't change its payout (recipient, amounts, fee, fee recipient, token,
  encrypted outputs). They *can* change the signer: this is intended, for relayers.
- G2b: they can't reveal its note's nullifier in a transaction of their own (front-running
  it) without the owner's secret key.

**G3 Liveness.** Funds don't get stuck.
- G3a: an honest owner's spend is accepted, unless a policy check or a limit (root window, tree
  capacity) blocks it.
- G3b: admins can't lock withdrawals: whatever fee settings and deposit limit they choose, a
  way to withdraw a note of at least 2 lamports exists, and at least half reaches the recipient.

**G4 Correct public payouts.** Public SOL moves only as those involved agreed.
- G4a: only accounts that signed pay, and at most what they agreed to.
- G4b: every account changes by exactly what it should receive minus what it should pay; the
  pool gains the external amount less the fee.

**G5 Admin control.** Only the authorities change the configuration, within limits.
- G5a: only admin changes signed by the initializer (the deployment's admin, if any) change it.
- G5b: the authorities never change, and the fees stay at most 100%.

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
G3a, G3b end in one; their titles mean "..., unless a hash break occurs". G4a, G4b, G5a and G5b
need none: they hold outright.

**Histories (`r : Run (initWorld params)`).** Everything that happened to the pool since it
was initialized:

    ws 0 ─updatedValues 0─▶ · ─txs[0]─▶ ws 1 ─updatedValues 1─▶ · ─txs[1]─▶ ws 2 ··· ws n = r.final
                                    │                                   │
                                  wit 0                               wit 1

- `ws 0 = initWorld params`: the freshly initialized pool.
- `txs[j]`: the `j`-th transaction the program accepted (`transact`).
- `updatedValues j`: the balances and config just before transaction `j`, after what happened
  outside `transact` since the previous one, limited to what Solana and the program allow
  (`UpdatedValuesBetweenTransacts.Allowed`): SOL sent to any account, other accounts spending,
  config changes signed by the right authority, each recorded with its signers.
- `ws j`: the world (pool state, balances, config) before `updatedValues j`.
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
- `[owner]`: the honest owner makes it true by following the protocol.
- `[premise]`: the situation the theorem is about (e.g. "this note is unspent"). It
  scopes the claim.
- `[limit]`: a check that can legitimately block a transaction: a protocol limit (root
  window, tree capacity, `u64` balances) or an admin setting (fee, deposit limit). The
  theorem says nothing when one is hit.
- `[assumption Tn]`: we rely on trusted assumption Tn above.  If Tn fails,
  the theorem says nothing about that run.

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
    - **genuine** (`GenuineInput`): it opens a leaf created by an earlier transaction (`< 2j`),
      the spender holds the note's key, and the spent note equals the note stored there; or
    - **a hash break** (`HashBreakInSpend`) occurs. -/
-- E: ok
def SpendsAreGenuine {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  -- For all txs, for both input amounts when they are an actual spend (not 0):
  ∀ j < r.txs.length, ∀ i : Fin 2, (wit j).inAmt i ≠ 0 →
    -- Either the note already existed among the first 2j leaves (the ones created by earlier txs),
    -- and the spender holds its key and states its real contents:
    GenuineInput wit (wit j) i (2 * j)
    -- Or there's a break with hash assumptions (T2)
    ∨ HashBreakInSpend r wit j i

/-- **G1a.** `SpendsAreGenuine` holds in every run from a freshly initialized pool.

Why this is the right statement: each of the three attacks makes the spent note differ from
the stored one. The stored note is taken from the accepted transactions themselves, not
chosen freely. -/
-- E: ok
theorem spends_are_genuine
    (params : InitParams)                                  -- [premise] the parameters the pool is initialized with
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [assumption T1] the witnesses of its proofs
    SpendsAreGenuine r wit :=
  fun j hj i hne => (LeanSpec.spends_are_genuine params r wit hwit j hj i hne).imp
    (fun h => GenuineInput.of_eq h) id

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
-- E: ok
def NoDoubleSpend {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  -- For any two inputs in the run that spend the same note,
  ∀ j < r.txs.length, ∀ j' < r.txs.length, ∀ i i' : Fin 2, DoubleSpend wit j i j' i' →
    -- a hash break occurs
    HashBreakInSpend r wit j i ∨ HashBreakInSpend r wit j' i' ∨ H1Collision ((wit j).inSk i) ((wit j').inSk i')

/-- **G1b.** `NoDoubleSpend` holds in every run from a freshly initialized pool.

Why this is the right statement: by G1a every spend opens the leaf holding exactly the note
it spends, so "a note is spent twice" means "two inputs open the same leaf". The two inputs
are any pair in the run, so both later and same-transaction re-spends are covered. -/
-- E: ok
theorem no_double_spend
    (params : InitParams)                                  -- [premise] the parameters the pool is initialized with
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [assumption T1] the witnesses of its proofs
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
-- E: ok
def PoolBacksNotes (params : InitParams) (r : Run (initWorld params)) (wit : ℕ → Witness) : Prop :=
  (r.final.poolBalance : ℤ) = params.rentExemptMin + ∑ pos ∈ r.unspent wit, leafValue wit pos + r.donated
  ∨ BreakInSomeSpend r wit

/-- **G1c.** `PoolBacksNotes` holds in every run from a freshly initialized pool.

Why this is the right statement:
- **notes vs. SOL, directly:** inflation means the notes are worth more than the SOL behind
  them, so the statement compares exactly those two.
- **an equality, not `≥`:** it rules out both inflation and leaks. With `≥`, donations
  could hide SOL leaking out of the pool; counting them exactly closes that gap. -/
-- E: ok
theorem balance
    (params : InitParams)                                  -- [premise] the parameters the pool is initialized with
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [assumption T1] the witnesses of its proofs
    PoolBacksNotes params r wit :=
  LeanSpec.balance params r wit hwit

/-! ### G1d. Only the owner's secret key can spend a note

In every run, a spend of a note uses the note owner's secret key, unless a hash break
occurs.

G1a only says the spender holds *a* key that hashes to the note's owner public key.
G1d says it is the owner's *own* key, unless someone found a second key with the same `H1` (`H1Collision`).-/

/-- The property G1d proves: `OnlyOwnerSpends r wit`: every spend in run `r` uses the
    owner's secret key, or a hash break occurs.

    If a non-zero input spends a note whose owner public key is `H1 skOwner`,
    then either:
    - **the owner's key:** the input's secret key is `skOwner`; or
    - **a hash break:** a `HashBreakInSpend` occurs, or `skOwner` and the input's key
      collide under `H1`. -/
-- E: ok
def OnlyOwnerSpends {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  ∀ j < r.txs.length, ∀ i : Fin 2, ∀ skOwner,
    -- if it is a real spend (input amount not 0)
    (wit j).inAmt i ≠ 0
    -- of a note owned by `H1 skOwner`,
    ∧ (leafNote wit (openedPos wit j i)).ownerPk = H1 skOwner →
    (wit j).inSk i = skOwner ∨ HashBreakInSpend r wit j i ∨ H1Collision skOwner ((wit j).inSk i)

/-- **G1d.** `OnlyOwnerSpends` holds in every run from a freshly initialized pool.-/
-- E: ok
theorem honest_note_spent_only_with_owner_key
    (params : InitParams)                                  -- [premise] the parameters the pool is initialized with
    (r : Run (initWorld params))                           -- [attacker] any history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :      -- [assumption T1] the witnesses of its proofs
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
    These checks are needed since the tx has not been processed, only submitted.
    -/
-- E: ok
def ExtDataWellFormed (T : TxInputs) : Prop :=
  externalDataBound T ∧ amountsInRange T.extAmt T.f ∧ encOutsFit T

/-- The property G2a proves: `SamePayout T T'`: the transactions `T` and `T'` pay out the
    same, or `sha256` collides.

    Either:
    - **same payout:** `T` and `T'` have the same recipient, amount, encrypted outputs,
      fee, fee recipient and token; or
    - **a hash break** (`Sha256Collision`): `sha256` collides on their serialized external
      data. -/
-- E: ok
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
-- E: ok
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
-- E: ok
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

An honest owner's spend is accepted, unless a policy check or a limit blocks it, if
it is blocked otherwise this is a break with assumptions.

Guards against: funds getting stuck because the program rejects an honest owner.

How it is stated: after any `Run`, suppose:
- the owner and the transaction are honest: everything the owner controls (`HonestSpend`),
- the known limits aren't hit: what can legitimately block the spend (`LimitsNotHit`).

Then either:
- the program accepts the transaction, with its own proof (`CanBeAccepted`), or
- some break with assumptions occurs (`SpendBlockedByBreak`).

`SpendBlockedByBreak` is one of:
- **pool drained** (`BreakInSomeSpend`): some earlier spend withdrew value no note backs
  (a forged spend or a double spend, G1c);
- **nullifier used first** (`NullifierTakenByCollision`): an earlier spend revealed the owner's
  nullifier from different arguments, i.e. an `H3` collision;
- **root is `0`** (`H2ZeroPreimage`): the tree's two top subtrees hash to `0`, i.e. an
  `H2` preimage of `0`.

Why the two hypotheses suffice: each check of `transact`, the fields of `HonestSpend` (`H`) and
`LimitsNotHit` (`L`) that ensure it, and the break that occurs if they don't ("or else").

| Check | Ensured by |
|---|---|
| `knownRoot` | `H.wellFormed.encodings`, `L.inWindow`; root `≠ 0` (`H.root`) or else `H2ZeroPreimage` |
| `externalDataBinding` | `H.wellFormed.externalData` |
| `minimumFee` | `L.fee` |
| `pubAmtConsistency` | `H.wellFormed.publicAmount` |
| `validZKP` | `H.wellFormed.validProof` |
| `newNullifiers` | `H.circuit`, `H.inputNotUsedBefore`, or else `NullifierTakenByCollision` |
| `distinctNullifiers` | `H.circuit` |
| `depositLimit` | `L.depositLimit` |
| `poolSolvency` | `H.genuine`, `H.notDoubleSpend`, `H.inputNotUsedBefore`, `H.root`, `H.circuit`, `H.wellFormed`, or else `BreakInSomeSpend` |
| `signerSolvency` | `H.signerCanPay` |
| `signerSignature` | `H.wellFormed.signed` |
| `treeNotFull` | `L.treeRoom` |
| `amountRange` | `H.wellFormed.amountRange` |
| `encOutLength` | `H.wellFormed.encOutLength` |
| `poolSeparate` | `H.wellFormed.poolSeparate` |
| `canonicalInputs` | `H.wellFormed.encodings` |
| `balancesFit` | `L.balancesFit` | -/

/-- **G3a.** An honest owner's spend is accepted, or an attacker-side hash break occurs. -/
theorem honest_spend_is_accepted
    (params : InitParams)                                  -- [premise] the parameters the pool is initialized with
    (r : Run (initWorld params))                           -- [attacker] any valid history
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)        -- [assumption T1] the witnesses of proofs of the attacker's run
    (inputs : TxInputs) (witness : Witness) (k : ℕ)        -- [owner] the honest owner's transaction, its
                                                           --   secrets, the tree state it uses
    (hHonest : HonestSpend r wit inputs witness k)         -- [owner]: everything the owner controls
    (hLimits : LimitsNotHit r.final inputs) :              -- [limit]: what can block it
    CanBeAccepted inputs r.final ∨ SpendBlockedByBreak r wit witness k :=
  LeanSpec.honest_spend_is_accepted params r wit hwit inputs witness k hHonest hLimits

/-! ### G3b. Admin config changes can't lock withdrawals

G3a takes the fee check passing as a limit, because a transaction's fee is fixed in its proof, so
it says nothing about hostile fee settings. This covers that: after any history, with any admin
changes, a way to withdraw notes worth `spentAmt` lamports in total exists. In the worst case
(withdrawal fee rate 100%, fee error margin 0) the fee check needs a fee equal to the payout,
because the rate applies to the payout and not to `spentAmt`; so at least half of `spentAmt`
reaches the recipient and the rest is the fee. The owner can name their own account as fee
recipient, so the whole of `spentAmt` can still come back to them. With the default settings the fee is about 0.25%.

Guards against: admins locking the funds in the pool through the fee settings or the deposit
limit.

Not covered: withdrawals can still be paused, by means other than the config:
- A program upgrade: the program's upgrade authority can deploy code that rejects withdrawals.
  The upgrade authority is outside the model.
- Off-chain services going down (relayer, indexer, frontend): the owner then can't easily build or
  submit the transaction. Here, we assume the owner's transaction and proof are given.

Other limits:
- A note of 1 lamport, which can't get out at a 100% withdrawal fee rate and a zero fee error margin.
- A config change after the transaction is built, which can make its fee too low; the owner then
  builds another. -/

/-- `WithdrawalWay c spentAmt payout fee`: under config `c`, taking `spentAmt` lamports out of the
    pool can pay `payout` to the recipient and `fee` to the fee recipient. -/
def WithdrawalWay (c : config) (spentAmt payout fee : ℕ) : Prop :=
  -- The recipient gets something,
  0 < payout
  -- all of `spentAmt` is paid out,
  ∧ payout + fee = spentAmt
  -- and the fee passes the fee check.
  ∧ feeSufficient c (-(payout : ℤ)) fee

/-- `WayIsAccepted r wit spentAmt payout fee`: after run `r`, an honest transaction that spends
    `spentAmt` and uses this split is accepted, unless something outside the admins' reach (an old
    root, a full tree, an overflow) or a hash break blocks it. -/
def WayIsAccepted {w0 : World} (r : Run w0) (wit : ℕ → Witness) (spentAmt payout fee : ℕ) : Prop :=
  ∀ (inputs : TxInputs) (witness : Witness) (k : ℕ)        -- [owner] the honest owner's transaction, its
                                                           --   secrets, the tree state it uses
    (_hHonest : HonestSpend r wit inputs witness k)        -- [owner] everything the owner controls
    (_hSpent : witness.inAmt 0 + witness.inAmt 1 = (spentAmt : F)) -- [premise] it spends inputs worth `spentAmt`
    (_hPayout : inputs.extAmt = -(payout : ℤ))             -- [owner] it pays `payout` to the recipient
    (_hFee : inputs.f = fee)                               -- [owner] and `fee` to the fee recipient
    (_hRoot : inputs.R ∈ Set.range r.final.state.tree.history) -- [limit] the root is still in the history
    (_hTree : treeHasRoom r.final.state.tree)              -- [limit] the tree is not full
    (_hFit : balancesFit inputs r.final),                  -- [limit] no credited balance overflows
    CanBeAccepted inputs r.final ∨ SpendBlockedByBreak r wit witness k

/-- **G3b.** After any run, with any admin changes, a way to withdraw notes worth `spentAmt`
    lamports exists, at least half of `spentAmt` (rounded down) reaches the recipient, and an
    honest transaction using that way is accepted (`WayIsAccepted`). -/
theorem admins_cannot_lock_withdrawals
    (params : InitParams)                                  -- [premise] the parameters the pool is initialized with
    (r : Run (initWorld params))                           -- [attacker] any valid history, with
                                                           --   any admin changes
    (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)        -- [assumption T1] the witnesses of proofs of the attacker's run
    (spentAmt : ℕ) (hSpentAmt : 2 ≤ spentAmt) :            -- [premise] the total of the notes the owner spends
    ∃ payout fee : ℕ,
      WithdrawalWay r.final.state.config spentAmt payout fee
      -- recipients gets at least half of the total
      ∧ spentAmt / 2 ≤ payout
      ∧ WayIsAccepted r wit spentAmt payout fee :=
  let ⟨payout, fee, h0, hsum, hfee, hhalf, hacc⟩ :=
    LeanSpec.admins_cannot_lock_withdrawals params r wit hwit spentAmt hSpentAmt
  ⟨payout, fee, ⟨h0, hsum, hfee⟩, hhalf,
    fun inputs witness k hH _ hA hF hW hR hB => hacc inputs witness k hH hA hF hW hR hB⟩

/-! ## G4. Correct public payouts -/

/-! ### G4a. Only accounts that signed pay, and at most what they agreed to

In every accepted transaction, an account other than the pool is debited only if it signed the
transaction, and then by at most its deposit plus the rent for the two nullifier accounts.

Guards against: taking SOL from an account that never signed, or charging the signer more than
the transaction says.-/

/-- The property G4a proves: `OnlySignersPay inputs old new`: in the transaction from `old` to
    `new`, every account other than the pool that is debited signed the transaction, and is
    debited by at most its deposit plus twice the nullifier rent. -/
def OnlySignersPay (inputs : TxInputs) (old new : World) : Prop :=
  ∀ (k : Pubkey)                                           -- [attacker] any account,
    (_hNotPool : k ≠ old.state.pool)                       -- [premise] other than the pool,
    (_hDebited : new.balances k < old.balances k),         -- [premise] that is debited:
    k ∈ inputs.signers ∧
      (old.balances k : ℤ) - new.balances k ≤ max inputs.extAmt 0 + 2 * old.nullifierRent

/-- **G4a.** `OnlySignersPay` holds for every accepted transaction. -/
theorem only_signers_pay
    (oldWorld newWorld : World) (inputs : TxInputs)        -- [attacker] any transaction, and the
                                                           --   pool before and after it
    (h : transact inputs oldWorld newWorld) :              -- [premise] the program accepted it
    OnlySignersPay inputs oldWorld newWorld :=
  fun k hk hlost => LeanSpec.only_signers_pay oldWorld newWorld inputs h k hk hlost

/-! ### G4b. Every account receives and pays exactly what it should

In every accepted transaction, the pool's SOL changes by `extAmt − f`, and every other account's
by exactly what it should receive minus what it should pay.

Guards against: underpaying or overpaying the recipient or the fee recipient, charging the
signer the wrong amount, paying or charging any other account, and SOL created or lost.-/

/-- `shouldReceive inputs k`: what the transaction should pay account `k`: `|extAmt|` if `k` is
    the recipient of a withdrawal, plus the fee `f` if `k` is the fee recipient. -/
def shouldReceive (inputs : TxInputs) (k : Pubkey) : ℤ :=
  -- withdrawal: the recipient `A` receives `|extAmt|`
  (if k = inputs.A ∧ inputs.extAmt < 0 then (inputs.extAmt.natAbs : ℤ) else 0)
  -- the fee recipient `t` receives the fee `f`
  + (if k = inputs.t then (inputs.f : ℤ) else 0)

/-- `shouldPay inputs rent k`: what account `k` should pay: the deposit `extAmt` if `k` is the
    signer of a deposit, plus `rent` for each of the two nullifier accounts if `k` is the signer. -/
def shouldPay (inputs : TxInputs) (rent : ℕ) (k : Pubkey) : ℤ :=
  -- deposit: the signer `s` pays `extAmt`
  (if k = inputs.s ∧ inputs.extAmt > 0 then inputs.extAmt else 0)
  -- the signer `s` pays rent for the two nullifier accounts
  + (if k = inputs.s then 2 * (rent : ℤ) else 0)

/-- The property G4b proves: `ExactPayouts inputs old new`: in the transaction from `old` to
    `new`, every account changes by exactly what it should receive minus what it should pay. -/
structure ExactPayouts (inputs : TxInputs) (old new : World) : Prop where
  /-- The pool gains the external amount, less the fee it pays out. -/
  pool : (new.poolBalance : ℤ) = old.poolBalance + inputs.extAmt - inputs.f
  /-- Every other account is credited what it should receive and debited what it should pay. -/
  others : ∀ k, k ≠ old.state.pool →
    (new.balances k : ℤ) =
      old.balances k + shouldReceive inputs k - shouldPay inputs old.nullifierRent k

/-- **G4b.** `ExactPayouts` holds for every accepted transaction. -/
theorem exact_payouts
    (oldWorld newWorld : World) (inputs : TxInputs)        -- [attacker] any transaction, and the
                                                           --   pool before and after it
    (h : transact inputs oldWorld newWorld) :              -- [premise] the program accepted it
    ExactPayouts inputs oldWorld newWorld :=
  have hp := LeanSpec.exact_payouts oldWorld newWorld inputs h
  ⟨hp.1, hp.2⟩

/-! ## G5. Admin control

A double check: G5a and G5b restate the admin rules of a run (`Allowed`, `AdminChange.apply`). -/

/-! ### G5a. Only the authorities change the configuration

Guards against: anyone else changing the config, or initializing the pool. -/

/-- `OnlyAuthoritiesChangeConfig params r`: the initializer is the deployment's admin (when it
    has one), and in every world of `r` the config is what the recorded admin changes produced,
    each signed by the initializer. -/
def OnlyAuthoritiesChangeConfig (params : InitParams) (r : Run (initWorld params)) : Prop :=
  -- the initializer is the deployment's admin, when it has one
  (∀ a, params.admin = some a → params.initializer = a) ∧
  -- for each world of the run
  ∀ j ≤ r.txs.length,
    -- the current config is what the run's admin changes produced
    ReachableByAdminChanges (r.adminChangesUpTo j) params.cfg (r.ws j).state.config ∧
    -- each of those changes was signed by the initializer
    (∀ ch ∈ r.adminChangesUpTo j, params.initializer ∈ ch.signers)

/-- **G5a.** `OnlyAuthoritiesChangeConfig` holds in every run from a freshly initialized pool. -/
theorem only_authorities_change_config
    (params : InitParams)                                  -- [premise] the parameters the pool is initialized with
    (r : Run (initWorld params)) :                         -- [attacker] any history
    OnlyAuthoritiesChangeConfig params r :=
  LeanSpec.only_authorities_change_config params r

/-! ### G5b. Admins change only the fees and the deposit limit, within bounds

Guards against: control passing to anyone else, and fees above 100% (G3b relies on this). -/

/-- `AdminPowersLimited params r`: in every world of `r`, both authorities are the initializer,
    and the fee error margin and both fee rates are at most 10000 basis points (100%). -/
def AdminPowersLimited (params : InitParams) (r : Run (initWorld params)) : Prop :=
  -- for each world of the run
  ∀ j ≤ r.txs.length,
    -- the authority stayed the same
    (r.ws j).state.config.authority = params.initializer ∧
    -- the limit authority stayed the same
    (r.ws j).state.config.limitAuthority = params.initializer ∧
    -- the fee error margin does not exceed the max allowed
    (r.ws j).state.config.feeErrorMargin ≤ 10000 ∧
    -- the two fee rates do not exceed the max allowed
    (r.ws j).state.config.depositFeeRate ≤ 10000 ∧
    (r.ws j).state.config.withdrawalFeeRate ≤ 10000

/-- **G5b.** `AdminPowersLimited` holds in every run from a freshly initialized pool. -/
theorem admin_powers_limited
    (params : InitParams)                                  -- [premise] the parameters the pool is initialized with
    (r : Run (initWorld params)) :                         -- [attacker] any history
    AdminPowersLimited params r :=
  LeanSpec.admin_powers_limited params r

end LeanSpec.Goals
