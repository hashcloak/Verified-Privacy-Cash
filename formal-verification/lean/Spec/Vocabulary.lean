import Spec.Spec

/-! # The definitions the theorem statements use

Part of the review surface (see `Spec/Statements.lean`). Only definitions, no proofs. -/

namespace LeanSpec
open PoseidonHashes Sha

variable [PoseidonHashes] [Sha] [Groups]
variable [AddCommGroup G1] [Module F G1] [AddCommGroup G2] [Module F G2] [CommGroup GT]
variable [Pairing] [Deployment]

-- HELPER: the full, zero-padded Merkle tree of `cs`, defined by plain recursion.
-- `foldAppend_spec` shows `appendEffects` computes exactly this tree.

/-- Leaf `i` of `cs`, or the zero leaf if `i` wasn't written. -/
def leafAt (cs : List F) (i : ℕ) : F :=
  if h : i < cs.length then cs[i] else Z 0

/-- Hash of the block of leaves `[idx * 2^height, (idx+1) * 2^height)`. -/
def treeHash (cs : List F) : ℕ → ℕ → F
  | 0, idx => leafAt cs idx
  | h+1, idx => H2 (treeHash cs h (2*idx)) (treeHash cs h (2*idx+1))

/-- Index, at height `h`, of the sibling of the block containing leaf `k`. -/
def siblingIdx (k h : ℕ) : ℕ := if Nat.testBit k h then k >>> h - 1 else k >>> h + 1

/-- The correct opening for leaf `k`: at each height, the sibling block's hash. Always
    valid (`calcRoot_canonicalOpening`), whether or not `k` was written. -/
def canonicalOpening (cs : List F) (k : Fin (2^26)) : Opening where
  index := k
  siblings := fun h => treeHash cs h.val (siblingIdx k.val h.val)

-- HELPER: turn `Fin.foldl` loops into plain `ℕ` recursion, so the 26-level folds can be
-- proved by ordinary induction.

/-- `foldUpTo f n x = f (⋯ (f (f x 0) 1) ⋯) (n-1)`: `Fin.foldl` without the `Fin`
    (`fin_foldl_eq_foldUpTo`). -/
def foldUpTo {α : Type} (f : α → ℕ → α) : ℕ → α → α
  | 0, x => x
  | k+1, x => f (foldUpTo f k x) k

/-- `Opening.calcRoot`'s per-level combination step, as a function of the plain `ℕ`
    height. -/
def stepFn (k : ℕ) (sib : ℕ → F) : F → ℕ → F :=
  fun acc h => if Nat.testBit k h then H2 (sib h) acc else H2 acc (sib h)

/-- The `H2` input pair at height `h`, used to state an `H2Collision`. -/
def stepPair (k : ℕ) (sib : ℕ → F) (acc : F) (h : ℕ) : F × F :=
  if Nat.testBit k h then (sib h, acc) else (acc, sib h)

/-- `O.siblings` as a plain `ℕ → F` (default `0` past height 26, never read). -/
def OpeningSib (O : Opening) : ℕ → F := fun h => if hh : h < 26 then O.siblings ⟨h,hh⟩ else 0

/-- A fake Merkle path that still reaches a real root: at some level, opening `O` (claiming
    leaf `c`) and the real path of the tree `cs` at the same position hash different pairs
    to the same value.

    Technically: an `H2Collision` between the `stepPair`s of the two paths at level `h`.
    All values are fixed by `cs`, `O` and `c`. -/
def PathCollision (cs : List F) (O : Opening) (c : F) : Prop :=
  ∃ h : Fin 26, H2Collision
    (stepPair O.index.val (OpeningSib O)
      (foldUpTo (stepFn O.index.val (OpeningSib O)) h.val c) h.val)
    (stepPair O.index.val (OpeningSib (canonicalOpening cs O.index))
      (foldUpTo (stepFn O.index.val (OpeningSib (canonicalOpening cs O.index))) h.val
        (leafAt cs O.index.val)) h.val)

--/////////////////////////////////////////
-- Runs: the vocabulary the theorems are stated in
--/////////////////////////////////////////

/-- A run is the history of the pool: the transactions the program accepted, in order,
    and the state of the pool before and after each one. Every theorem is about every
    possible history starting from the freshly initialized pool, so it holds whatever
    transactions were submitted.

    Technical: `txs` is the list of accepted transactions, starting from world `w0`.
    `ws j` is the world before transaction `j` (so `ws 0 = w0`), and `ws txs.length` is the
    final world. `step` says each transaction is accepted (`transact`) and leads to the
    next world. Every theorem uses `w0 = initWorld params`; `w0` is a
    parameter only so some lemmas don't need those arguments. This is ghost data: the
    program doesn't store it; it exists only to state the theorems. -/
structure Run (w0 : World) where
  txs : List TxInputs
  ws : ℕ → World
  start : ws 0 = w0
  step : ∀ j (h : j < txs.length), transact txs[j] (ws j) (ws (j+1))

/-- The state of the pool at the end of the history. -/
def Run.final {w0 : World} (r : Run w0) : World := r.ws r.txs.length

/-- The note commitments these transactions add to the tree, in order.

    Technical: two commitments per transaction (`outC0`, then `outC1`), so leaves `2j` and
    `2j+1` come from transaction `j`. -/
def leaves (txs : List TxInputs) : List F := txs.flatMap (fun tx => [tx.outC0, tx.outC1])

/-- The witness data behind the proofs of the history: for each transaction whose proof
    verifies, the secret data that proof attests to.

    Technical: if the proof of transaction `j` verifies (`proofValid`), `wit j` satisfies the
    circuit relation `RelationS` for its public inputs. Read as the knowledge extractor's
    output (T1). Every accepted transaction's proof verifies (G1e), so this gives a witness
    for every transaction of a run (`WitnessesFor.relation`); for a transaction whose proof
    was never checked it would give none. A toy-model check shows such witnesses can exist
    (`NonVacuity.run_with_spend_exists`). -/
def Run.WitnessesFor {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  ∀ j (h : j < r.txs.length), proofValid r.txs[j] → RelationS r.txs[j].pubInputs (wit j)

/-- The note spent by input `i`: amount, owner public key, blinding factor, token (mint). -/
def Witness.inNote (w : Witness) (i : Fin 2) : Note :=
  ⟨w.inAmt i, w.inPk i, w.inR i, w.mint⟩

/-- The note created by output `o`: amount, owner public key, blinding factor, token (mint). -/
def Witness.outNote (w : Witness) (o : Fin 2) : Note :=
  ⟨w.outAmt o, w.outPk o, w.outR o, w.mint⟩

/-- The tree position of the note that input `i` of transaction `j` spends.

    Technically: the leaf index of that input's Merkle opening. -/
def spentLeaf (wit : ℕ → Witness) (j : ℕ) (i : Fin 2) : ℕ := ((wit j).openings i).index.val

/-- The note stored at tree position `pos`, as created by the transaction that added it.

    Technically: leaf `pos` is output `pos % 2` of transaction `pos / 2`, read from that
    transaction's witness. -/
def leafNote (wit : ℕ → Witness) (pos : ℕ) : Note :=
  (wit (pos / 2)).outNote ⟨pos % 2, Nat.mod_lt _ (by norm_num)⟩

/-- The amount of the note at tree position `pos`, as an integer. -/
def leafValue (wit : ℕ → Witness) (pos : ℕ) : ℤ := ((leafNote wit pos).amount.val : ℤ)

/-- The hash breaks a forged spend would need. If a spend (input `i` of transaction `j`)
    doesn't match a real note, one of these happened:
    - its Merkle path is fake: it collides with the real path of the tree (`H2`);
    - it opens an empty tree position, so its note must hash to `0` (`H4`);
    - it opens a real note but claims different contents with the same hash (`H4`).

    Technically: the first case compares against the tree after its first `k` leaves, for
    some `k ≤ 2j` (a state of the tree before transaction `j`). All values are computed
    from the history and the witnesses, so each case is a specific collision. -/
def SpendBreak {w0 : World} (r : Run w0) (wit : ℕ → Witness) (j : ℕ) (i : Fin 2) : Prop :=
  (∃ k ≤ 2 * j, PathCollision ((leaves (r.txs.take j)).take k) ((wit j).openings i) ((wit j).inC i))
  ∨ H4ZeroPreimage ((wit j).inNote i)
  ∨ H4Collision ((wit j).inNote i) (leafNote wit (spentLeaf wit j i))

open Classical in
/-- The tree positions holding notes that have not been spent.

    Technically: positions below `2 · txs.length` that no non-zero input of any transaction
    opens. -/
noncomputable def Run.unspent {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Finset ℕ :=
  (Finset.range (2 * r.txs.length)).filter
    (fun pos => ¬ ∃ j < r.txs.length, ∃ i, (wit j).inAmt i ≠ 0 ∧ spentLeaf wit j i = pos)

/-- The hash breaks the balance proof (G1c) can fall back on: some spend exposes a
    `SpendBreak`, or two different spends of the same tree position use secret keys that
    collide under `H1`.

    Technically: the two failure cases of G1a and G1b, over every spend of the run. -/
def BalanceBreak {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  (∃ j < r.txs.length, ∃ i, (wit j).inAmt i ≠ 0 ∧ SpendBreak r wit j i)
  ∨ (∃ j < r.txs.length, ∃ j' < r.txs.length, ∃ i i', (wit j).inAmt i ≠ 0 ∧ (wit j').inAmt i' ≠ 0
      ∧ (j, i) ≠ (j', i') ∧ spentLeaf wit j i = spentLeaf wit j' i'
      ∧ H1Collision ((wit j).inSk i) ((wit j').inSk i'))

/-- The three values hashed into the nullifier of input `i`: the note commitment, its tree
    position and the owner's signature. -/
def Witness.nullifierArgs (w : Witness) (i : Fin 2) : F × F × F :=
  (w.inC i, (w.openings i).index, w.sign i)

/-- How the nullifier of an owner's note (input `i` of witness `w`, with non-zero amount)
    could already be used up by a transaction of the run without spending the note: only
    through a hash collision.

    Technically: input `i'` of transaction `j` revealed that nullifier, and an `H3` or `H4`
    collision occurs between the two inputs' values. -/
def NullifierTaken {w0 : World} (r : Run w0) (wit : ℕ → Witness) (w : Witness) (i : Fin 2) : Prop :=
  ∃ j, ∃ (hj : j < r.txs.length), ∃ i',
    r.txs[j].pubInputs.nullifiers i' = nullifier (w.inC i) (w.sign i) (w.openings i).index
    ∧ (H3Collision (w.nullifierArgs i) ((wit j).nullifierArgs i')
       ∨ H4Collision (w.inNote i) ((wit j).inNote i'))

/-- The three values hashed into the signature of input `i`: the secret key, the note
    commitment and its tree position. -/
def Witness.signatureArgs (w : Witness) (i : Fin 2) : F × F × F :=
  (w.inSk i, w.inC i, (w.openings i).index)

/-- How the nullifier of a zero-amount ("dummy") input `i` of witness `w`, whose secret key
    no input of the run uses, could already be used up: only through a hash collision.

    Technically: input `i'` of transaction `j` revealed that nullifier, and an `H3`
    collision occurs, either on the nullifier's arguments or on the signature's. -/
def DummyNullifierTaken {w0 : World} (r : Run w0) (wit : ℕ → Witness) (w : Witness) (i : Fin 2) : Prop :=
  ∃ j, ∃ (hj : j < r.txs.length), ∃ i',
    r.txs[j].pubInputs.nullifiers i' = nullifier (w.inC i) (w.sign i) (w.openings i).index
    ∧ (H3Collision (w.nullifierArgs i) ((wit j).nullifierArgs i')
       ∨ H3Collision (w.signatureArgs i) ((wit j).signatureArgs i'))


/-! ### The pieces of G3a (liveness)

Each field is tagged with who controls it (see "Who controls each hypothesis" in the goals
header). -/

/-- The root a spend uses: the root of the tree's first `k` leaves, still in the root
    history. -/
structure RootInWindow {w0 : World} (r : Run w0) (R : F) (k : ℕ) : Prop where
  /-- [owner] The spend uses the tree as it was after its first `k` leaves... -/
  isPrefix : k ≤ 2 * r.txs.length
  /-- [owner] ...and that tree's root. -/
  isPrefixRoot : R = (foldAppend ((leaves r.txs).take k) initTree).root
  /-- [limit] That root has not left the 100-slot root history yet. -/
  inWindow : R ∈ Set.range r.final.state.tree.history

/-- The owner's input notes: unspent notes of the run, in the tree under the spend's root.
    `witness` holds the owner's secrets for the spend; `wit` the witnesses of the run. -/
structure OwnsUnspentNotes {w0 : World} (r : Run w0) (wit : ℕ → Witness) (witness : Witness)
    (k : ℕ) : Prop where
  /-- [premise] No spend of the run has opened the owner's notes. -/
  unspent : ∀ i, witness.inAmt i ≠ 0 → (witness.openings i).index.val ∈ r.unspent wit
  /-- [owner] Each note was in the tree under the spend's root (one of the first `k` leaves). -/
  inTree : ∀ i, witness.inAmt i ≠ 0 → (witness.openings i).index.val < k
  /-- [owner] The owner states its notes' real contents. -/
  isOwnersNote : ∀ i, witness.inAmt i ≠ 0 →
    witness.inNote i = leafNote wit (witness.openings i).index.val
  /-- [owner] Two non-zero inputs spend two different notes. -/
  different : witness.inAmt 0 ≠ 0 → witness.inAmt 1 ≠ 0 →
    (witness.openings 0).index ≠ (witness.openings 1).index
  /-- [owner] Each zero-amount input uses a fresh secret key: one no input of the run uses. -/
  freshDummyKeys : ∀ i, witness.inAmt i = 0 →
    ∀ j < r.txs.length, ∀ i', (wit j).inSk i' ≠ witness.inSk i

/-- [owner] The transaction is built honestly from the owner's secrets `witness`, in world `w`. -/
structure BuiltHonestly (w : World) (inputs : TxInputs) (witness : Witness) : Prop where
  outputs : ∀ j, inputs.pubInputs.outCommitments j
    = commit (witness.outAmt j) (witness.outPk j) (witness.outR j) witness.mint
  nullifiers : ∀ i, inputs.pubInputs.nullifiers i
    = nullifier (witness.inC i) (witness.sign i) (witness.openings i).index
  amounts : witness.inAmt 0 + witness.inAmt 1 + inputs.pubInputs.pubAmt
    = witness.outAmt 0 + witness.outAmt 1
  outputRange : ∀ j, (witness.outAmt j).val < 2^248
  externalData : externalDataBound inputs
  publicAmount : pubAmtConsistent inputs.extAmt inputs.f inputs.pubAmt
  distinctNullifiers : nullifiersDistinct inputs.k0 inputs.k1
  amountRange : amountsInRange inputs.extAmt inputs.f
  encOutLength : encOutsFit inputs
  poolSeparate : poolIsSeparate inputs w.state.pool
  /-- The signer's account can pay the rent for the two nullifier accounts and the deposit. -/
  signerCanPay : signerSolvent w.balances inputs.s inputs.extAmt w.nullifierRent

/-- The program's policy checks pass in world `w`. These can legitimately block a spend. -/
structure PolicyChecksPass (w : World) (inputs : TxInputs) : Prop where
  /-- [policy] -/
  fee : feeSufficient w.state.config inputs.extAmt inputs.f
  /-- [policy] -/
  depositLimit : depositWithinLimit w.state.config inputs.extAmt
  /-- [policy] Stricter than the code (`hDevPool`): the spec checks the pool before the
      deposit lands, so it rejects e.g. the first fee-paying deposit into an empty pool. -/
  depositFee : inputs.extAmt ≥ 0 ∧ inputs.f > 0 → w.poolBalance ≥ inputs.f + w.rentExemptMin
  /-- [limit] The tree is not full (G3c). -/
  treeRoom : treeHasRoom w.state.tree

/-- The program accepts `inputs` in world `w`, with some proof. -/
def CanBeAccepted (inputs : TxInputs) (w : World) : Prop :=
  ∃ π, transact { inputs with π := π } w (transactEffects { inputs with π := π } w)

/-- The attacker-side hash breaks that could stop an honest spend:
    - the spend's root is `0`, so its two subtrees are an `H2` preimage of `0`;
    - a `BalanceBreak` (G1c);
    - the nullifier of one of the owner's inputs was taken through a hash collision
      (`NullifierTaken` for a real note, `DummyNullifierTaken` for a zero-amount input). -/
def LivenessBreak {w0 : World} (r : Run w0) (wit : ℕ → Witness) (witness : Witness) (k : ℕ) : Prop :=
  H2ZeroPreimage (treeHash ((leaves r.txs).take k) 25 0, treeHash ((leaves r.txs).take k) 25 1)
  ∨ BalanceBreak r wit
  ∨ (∃ i, witness.inAmt i ≠ 0 ∧ NullifierTaken r wit witness i)
  ∨ (∃ i, witness.inAmt i = 0 ∧ DummyNullifierTaken r wit witness i)


end LeanSpec
