import Spec.Spec

/-! # The definitions the theorem statements use

Part of the review surface (see `Spec/Statements.lean`). Only definitions, no proofs. -/

namespace LeanSpec
open PoseidonHashes Sha

variable [PoseidonHashes] [Sha] [Groups]
variable [AddCommGroup G1] [Module F G1] [AddCommGroup G2] [Module F G2] [CommGroup GT]
variable [Pairing] [Deployment]

/-- `leafAt cs i`: leaf `i`, or the zero leaf if `i` wasn't written.
  The tree has leaves `cs`. -/
def leafAt (cs : List F) (i : ℕ) : F :=
  if h : i < cs.length then cs[i] else Z 0

/-- `treeHash cs height idx`: the hash of node `idx` at level `height` (0 = level of leaves).
    The tree has leaves `cs`. -/
def treeHash (cs : List F) : ℕ → ℕ → F
  | 0, idx => leafAt cs idx
  | h+1, idx => H2 (treeHash cs h (2*idx)) (treeHash cs h (2*idx+1))

/-- `realInputsAt cs k h`: the two values the real Merkle path of leaf `k` hashes at level
    `h`, in the tree with leaves `cs`: the two children of its node at level `h+1`. -/
def realInputsAt (cs : List F) (k h : ℕ) : F × F :=
  let m := k / 2^(h+1)
  (treeHash cs h (2*m), treeHash cs h (2*m+1))

/-- `O.sibling h`: the sibling hash opening `O` gives at level `h` (`0` past level 25). -/
def Opening.sibling (O : Opening) (h : ℕ) : F := if hh : h < 26 then O.siblings ⟨h, hh⟩ else 0

/-- `O.nodeAt leaf h`: the hash reached after `h` levels, going up from `leaf` along
    opening `O`.

    - **the ends:** level 0 is the leaf itself; level 26 is the root `Opening.calcRoot`
      computes;
    - **left or right:** at each level, bit `h` of the index says whether the node so far
      is the right or the left input of `H2`. -/
def Opening.nodeAt (O : Opening) (leaf : F) : ℕ → F
  | 0 => leaf
  | h + 1 => if Nat.testBit O.index.val h then H2 (O.sibling h) (O.nodeAt leaf h)
      else H2 (O.nodeAt leaf h) (O.sibling h)

/-- `O.inputsAt leaf h`: the two values `H2` combines at level `h`, going up from `leaf`
    along opening `O`: the node reached so far and the sibling, in the order bit `h` of the
    index gives. -/
def Opening.inputsAt (O : Opening) (leaf : F) (h : ℕ) : F × F :=
  if Nat.testBit O.index.val h then (O.sibling h, O.nodeAt leaf h) else (O.nodeAt leaf h, O.sibling h)

/-- `PathCollision cs O c`: a fake Merkle path reaches a real root through an `H2`
    collision.

    At some level `h`, two paths feed different pairs to `H2` with the same
    output:
    - **the claimed path:** opening `O`, going up from the claimed leaf `c`;
    - **the real path:** in the tree with leaves `cs`, at the same position.
    All values are fixed by `cs`, `O` and `c`, so this is one specific collision. -/
def PathCollision (cs : List F) (O : Opening) (c : F) : Prop :=
  ∃ h : Fin 26, H2Collision (O.inputsAt c h)
    (realInputsAt cs O.index.val h)

--/////////////////////////////////////////
-- Runs: the vocabulary the theorems are stated in
--/////////////////////////////////////////

/-- `Run w0`: a history of the pool starting from world `w0`: the transactions the program
    accepted, in order, and what happened between them.

    - **the transactions** (`txs`): the accepted transactions, in order;
    - **the worlds** (`ws`): `ws j` is the world before transaction `j` (so `ws 0 = w0`),
      and `ws txs.length` is the final world;
    - **what happened in between** (`between j`, just before transaction `j`): SOL sent to
      the pool or to other accounts, other accounts spent from, admin changes to the
      config. `allowed`: Solana and the program allow it (`Between.Allowed`). `between 0`
      includes SOL sent to the pool before `initialize`;
    - **each step is accepted** (`step`): transaction `j` is accepted (`transact`) from
      world `j` updated by `between j`, and leads to world `j + 1`.
    What happens after the last transaction is not part of the run.

    How the theorems use it: each quantifies over all runs from `initWorld params`, so it
    holds whatever transactions were submitted and whatever happened between them. (`w0`
    is a parameter only so some lemmas need fewer arguments.) A run is ghost data: the
    program doesn't store it; it exists only to state the theorems. -/
structure Run (w0 : World) where
  txs : List TxInputs
  ws : ℕ → World
  between : ℕ → Between
  start : ws 0 = w0
  allowed : ∀ j < txs.length, (between j).Allowed (ws j)
  step : ∀ j (h : j < txs.length), transact txs[j] ((ws j).between (between j)) (ws (j+1))

/-- `r.donations j`: the SOL sent to the pool from outside just before transaction `j`
    (the pool can only gain then). -/
def Run.donations {w0 : World} (r : Run w0) (j : ℕ) : ℕ :=
  (r.between j).balances (r.ws j).state.pool - (r.ws j).poolBalance

/-- `r.donated`: the SOL sent to the pool from outside during the run, summed over the
    gaps before each transaction. -/
def Run.donated {w0 : World} (r : Run w0) : ℕ :=
  ∑ j ∈ Finset.range r.txs.length, r.donations j

/-- `r.final`: the world right after the last transaction of the run. -/
def Run.final {w0 : World} (r : Run w0) : World := r.ws r.txs.length

/-- `leaves txs`: the note commitments these transactions add to the tree, in order.

    Two per transaction (`outC0`, then `outC1`), so leaves `2j` and `2j+1`
    come from transaction `j`. -/
def leaves (txs : List TxInputs) : List F := txs.flatMap (fun tx => [tx.outC0, tx.outC1])

/-- `r.firstLeaves k`: the first `k` leaves the run's transactions add to the tree. -/
def Run.firstLeaves {w0 : World} (r : Run w0) (k : ℕ) : List F := (leaves r.txs).take k

/-- `r.WitnessesFor wit`: `wit` assigns a valid witness to every proof of the run `r`.

    It should hold that for each transaction `j` of `r`:
    - if its proof verifies (`proofValid`),
    - then `wit j` (input notes, secret keys, Merkle paths, output notes) satisfies the
      circuit (`RelationS`) for transaction `j`'s public inputs.

    The theorems use `wit` to talk about which notes a transaction spends and with which
    keys; since we assume T1, whoever made transaction `j` knows `wit j`. -/
def Run.WitnessesFor {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  -- For all transactions in the run, if the proof if valid => relation S holds for witness for j
  ∀ j (h : j < r.txs.length), proofValid r.txs[j] → RelationS r.txs[j].pubInputs (wit j)

/-- `w.inNote i`: the note input `i` of witness `w` spends: amount, owner public key,
    blinding factor, token (mint). -/
def Witness.inNote (w : Witness) (i : Fin 2) : Note :=
  ⟨w.inAmt i, w.inPk i, w.inR i, w.mint⟩

/-- `w.outNote o`: the note output `o` of witness `w` creates: amount, owner public key,
    blinding factor, token (mint). -/
def Witness.outNote (w : Witness) (o : Fin 2) : Note :=
  ⟨w.outAmt o, w.outPk o, w.outR o, w.mint⟩

/-- `openedPos wit j i`: the tree position that input `i` of transaction `j` opens, i.e. the
    leaf index of that input's Merkle opening. For a non-zero input, the position of the
    note it spends; for a dummy (zero-amount) input, an arbitrary position. -/
def openedPos (wit : ℕ → Witness) (j : ℕ) (i : Fin 2) : ℕ := ((wit j).openings i).index.val

/-- `leafNote wit pos`: the note stored at tree position `pos`, as created by the
    transaction that added it.

    The tree holds only the commitment, so the note itself is read from that transaction's witness.
    Which transaction: each transaction appends its two output commitments in order
    (transaction 0 writes leaves 0 and 1, transaction 1 leaves 2 and 3, …), so leaf `pos`
    is output `pos % 2` of transaction `pos / 2` -/
def leafNote (wit : ℕ → Witness) (pos : ℕ) : Note :=
  let tx := pos / 2
  -- Parse the pos % 2 to a Fin 2
  let output : Fin 2 := ⟨pos % 2, Nat.mod_lt _ (by norm_num)⟩
  (wit tx).outNote output

/-- `leafValue wit pos`: the amount of the note at tree position `pos`, as an integer. -/
def leafValue (wit : ℕ → Witness) (pos : ℕ) : ℤ := ((leafNote wit pos).amount.val : ℤ)

/-- `HashBreakInSpend r wit j i`: one of three specific hash breaks occurs at the spend
    by input `i` of transaction `j`.

    One of:
    - **A fake Merkle path** (`PathCollision`, `H2`): the spend's path differs from the
      real path at its position, yet reaches the same root. The real path is the one in the
      tree as it was when its root was the spend's root: the tree's first `k` leaves
      (`k ≤ 2j`). A spend may use an old root, so the comparison must be with the old tree.
    - **A note at an empty position** (`H4ZeroPreimage`): the spend opens a position with
      no note (leaf `0`), so its note's commitment is `0`.
    - **Wrong contents for a real note** (`H4Collision`): the spend opens a real note but
      claims a different key, amount or token with the same commitment.
    -/
def HashBreakInSpend {w0 : World} (r : Run w0) (wit : ℕ → Witness) (j : ℕ) (i : Fin 2) : Prop :=
  (∃ k ≤ 2 * j, PathCollision ((leaves (r.txs.take j)).take k) ((wit j).openings i) ((wit j).inC i))
  ∨ H4ZeroPreimage ((wit j).inNote i)
  ∨ H4Collision ((wit j).inNote i) (leafNote wit (openedPos wit j i))

open Classical in
/-- `r.unspent wit`: the tree positions holding notes not yet spent in the run.

    The positions below `2 · txs.length` that no non-zero input of any
    transaction opens. -/
noncomputable def Run.unspent {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Finset ℕ :=
  (Finset.range (2 * r.txs.length)).filter
    (fun pos => ¬ ∃ j < r.txs.length, ∃ i, (wit j).inAmt i ≠ 0 ∧ openedPos wit j i = pos)

/-- `DoubleSpend wit j i j' i'`: input `i` of transaction `j` and input `i'` of transaction
    `j'` are two different real spends of the same tree position. -/
    -- E: ok
def DoubleSpend (wit : ℕ → Witness) (j : ℕ) (i : Fin 2) (j' : ℕ) (i' : Fin 2) : Prop :=
  -- two different inputs (possibly of the same transaction),
  (j, i) ≠ (j', i')
  -- both real spends (input amount not 0),
  ∧ (wit j).inAmt i ≠ 0 ∧ (wit j').inAmt i' ≠ 0
  -- that open the same position in the tree
  ∧ openedPos wit j i = openedPos wit j' i'

/-- `BreakInSomeSpend r wit`: one of the breaks of G1a or G1b occurs at some spend of the
    run: a forged spend or a double spend. It is G1c's failure case.

    Options:
    - **a forged spend** (G1a fails): some real spend of the run has a `HashBreakInSpend`;
    - **a double spend** (G1b fails): two different real spends open the same tree position,
      with two different secret keys for the same public key (`H1Collision`). -/
def BreakInSomeSpend {w0 : World} (r : Run w0) (wit : ℕ → Witness) : Prop :=
  -- Either for a txs in the run
  (∃ j < r.txs.length, ∃ i,
    -- that is a real spend (input amount not 0)
    (wit j).inAmt i ≠ 0
    -- leads to a break,
    ∧ HashBreakInSpend r wit j i)
  -- or two inputs of the run spend the same note
  ∨ (∃ j < r.txs.length, ∃ j' < r.txs.length, ∃ i i', DoubleSpend wit j i j' i'
      -- and lead to a break.
      ∧ H1Collision ((wit j).inSk i) ((wit j').inSk i'))

/-- `w.nullifierArgs i`: the three values hashed (`H3`) into the nullifier of input `i`:
    the note commitment, its tree position and the owner's signature. -/
def Witness.nullifierArgs (w : Witness) (i : Fin 2) : F × F × F :=
  (w.inC i, (w.openings i).index, w.sign i)

/-- `w.inNullifier i`: the nullifier input `i` of witness `w` reveals. -/
def Witness.inNullifier (w : Witness) (i : Fin 2) : F :=
  nullifier (w.inC i) (w.sign i) (w.openings i).index

/-- `NullifierCollision w i w' i'`: input `i` of `w` and input `i'` of `w'` reveal the same
    nullifier without being the same note at the same position. A nullifier is
    `H3 (commitment, position, signature)`, so this needs one of:
    - **different `H3` inputs** (`H3Collision`): the two triples differ but hash to the same
      nullifier;
    - **equal `H3` inputs, different notes** (`H4Collision`): the commitments are equal, but
      the notes behind them differ. -/
def NullifierCollision (w : Witness) (i : Fin 2) (w' : Witness) (i' : Fin 2) : Prop :=
  H3Collision (w.nullifierArgs i) (w'.nullifierArgs i') ∨ H4Collision (w.inNote i) (w'.inNote i')

/-- `NullifierTaken r wit w i`: the nullifier of an owner's real note (input `i` of `w`) was
    already revealed in the run through a hash collision, without the note being spent: some
    input `i'` of some transaction `j` revealed it, with a `NullifierCollision`. -/
def NullifierTaken {w0 : World} (r : Run w0) (wit : ℕ → Witness) (w : Witness) (i : Fin 2) : Prop :=
  ∃ j, ∃ (hj : j < r.txs.length), ∃ i',
    r.txs[j].pubInputs.nullifiers i' = w.inNullifier i
    ∧ NullifierCollision w i (wit j) i'

/-- `w.signatureArgs i`: the three values hashed (`H3`) into the signature of input `i`:
    the secret key, the note commitment and its tree position. -/
def Witness.signatureArgs (w : Witness) (i : Fin 2) : F × F × F :=
  (w.inSk i, w.inC i, (w.openings i).index)

/-- `DummyNullifierTaken r wit w i`: the nullifier of a zero-amount ("dummy") input `i` of
    `w`, whose secret key no input of the run uses, was already revealed in the run through
    a hash collision.

    Some input `i'` of some transaction `j` revealed that nullifier, and
    either:
    - **same nullifier, different arguments** (`H3`): the two inputs' nullifier arguments
      collide; or
    - **same signature, different arguments** (`H3`): the two inputs' signature arguments
      collide. -/
def DummyNullifierTaken {w0 : World} (r : Run w0) (wit : ℕ → Witness) (w : Witness) (i : Fin 2) : Prop :=
  ∃ j, ∃ (hj : j < r.txs.length), ∃ i',
    r.txs[j].pubInputs.nullifiers i' = w.inNullifier i
    ∧ (H3Collision (w.nullifierArgs i) ((wit j).nullifierArgs i')
       ∨ H3Collision (w.signatureArgs i) ((wit j).signatureArgs i'))


/-! ### The pieces of G3a (liveness)

Each field is tagged with where it comes from (see "Where each hypothesis comes from" in
`Spec/Statements.lean`). -/

/-- `RootInWindow r R k`: the spend's root `R` is a real past root of the run that the
    program still accepts.

    - **a real past root:** `R` is the root of the tree after its first `k` leaves, for
      some `k` up to the end of the run;
    - **still accepted:** `R` is still in the 100-slot root history at the end of the
      run. -/
structure RootInWindow {w0 : World} (r : Run w0) (R : F) (k : ℕ) : Prop where
  /-- [owner] The spend uses the tree as it was after its first `k` leaves... -/
  isPrefix : k ≤ 2 * r.txs.length
  /-- [owner] ...and that tree's root. -/
  isPrefixRoot : R = (foldAppend (r.firstLeaves k) initTree).root
  /-- [limit] That root has not left the 100-slot root history yet. -/
  inWindow : R ∈ Set.range r.final.state.tree.history

/-- `OwnsUnspentNotes r wit witness k`: the owner's spend (secrets `witness`) spends real,
    unspent notes of the run, in the tree under the spend's root (the first `k` leaves).

    One field each:
    - **real notes** (non-zero inputs): unspent, in the tree under the root, with the
      note's real contents, and two inputs spend different notes;
    - **dummy inputs** (zero amount): each uses a fresh secret key.
    `wit` are the witnesses of the run. -/
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

/-- [owner] `BuiltHonestly w inputs witness`: the transaction `inputs` is built honestly
    from the owner's secrets `witness`, in world `w`.

    - **computed from the secrets:** the output commitments and nullifiers are computed
      from `witness`, and the amounts balance;
    - **well formed:** the transaction meets the spec's preconditions on ranges,
      encodings, the pool kept separate, and the signer being able to pay. -/
structure BuiltHonestly (w : World) (inputs : TxInputs) (witness : Witness) : Prop where
  outputs : ∀ j, inputs.pubInputs.outCommitments j
    = commit (witness.outAmt j) (witness.outPk j) (witness.outR j) witness.mint
  nullifiers : ∀ i, inputs.pubInputs.nullifiers i
    = witness.inNullifier i
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
  /-- The seven public inputs are sent as their canonical encodings. -/
  encodings : publicInputsEncoded inputs

/-- `PolicyChecksPass w inputs`: the program's policy checks and limits pass for `inputs` in
    world `w`. These are the checks that can legitimately block a spend.

    - **policy checks:** the fee is sufficient, the deposit is within the limit, and a
      deposit with a fee leaves the pool its rent reserve;
    - **limits:** the tree has room, and no credited balance overflows a `u64`. -/
structure PolicyChecksPass (w : World) (inputs : TxInputs) : Prop where
  /-- [policy] -/
  fee : feeSufficient w.state.config inputs.extAmt inputs.f
  /-- [policy] -/
  depositLimit : depositWithinLimit w.state.config inputs.extAmt
  /-- [policy] On a deposit with a fee, the pool (with the deposit) covers the fee and keeps
      its rent reserve. -/
  depositFee : inputs.extAmt ≥ 0 ∧ inputs.f > 0 →
    (w.poolBalance : ℤ) + inputs.extAmt ≥ inputs.f + w.rentExemptMin
  /-- [limit] The tree is not full (G3c). -/
  treeRoom : treeHasRoom w.state.tree
  /-- [limit] No balance a payment credits overflows a `u64` (unreachable in practice: 2^64
      lamports exceeds the total SOL supply). -/
  balancesFit : balancesFit inputs w

/-- `CanBeAccepted inputs w`: the program accepts `inputs` in world `w`, with some proof. -/
def CanBeAccepted (inputs : TxInputs) (w : World) : Prop :=
  ∃ π, transact { inputs with π := π } w (transactEffects { inputs with π := π } w)

/-- `SpendBlockedByBreak r wit witness k`: an attacker blocked the owner's honest spend
    (`witness`, against the root of the first `k` leaves), which needs a hash break.

    To make the program reject the spend, the attacker must defeat one of its checks:
    - **drain the pool** (`BreakInSomeSpend`): to leave too little SOL for the owner's
      withdrawal, the attacker must withdraw value no note backs: forge a spend or spend a
      note twice (G1c);
    - **use up the owner's nullifier** (`NullifierTaken` for a real note,
      `DummyNullifierTaken` for a zero-amount input): the program rejects a nullifier
      already used. To use it first, the attacker must reveal it from a different note,
      position or key, i.e. find an `H3` or `H4` collision (G3b);
    - **make the root `0`** (`H2ZeroPreimage`): the program rejects the root `0`. To make
      the tree's root `0`, the attacker must add leaves whose two top subtrees hash to `0`,
      i.e. find an `H2` preimage of `0`. -/
def SpendBlockedByBreak {w0 : World} (r : Run w0) (wit : ℕ → Witness) (witness : Witness) (k : ℕ) : Prop :=
  -- Drain pool by breaking spending
  BreakInSomeSpend r wit
  -- or, already use the nullifiers
  ∨ (∃ i, witness.inAmt i ≠ 0 ∧ NullifierTaken r wit witness i)
  ∨ (∃ i, witness.inAmt i = 0 ∧ DummyNullifierTaken r wit witness i)
  -- or the 2 last nodes hash together to obtain 0
  ∨ H2ZeroPreimage (treeHash (r.firstLeaves k) 25 0, treeHash (r.firstLeaves k) 25 1)

end LeanSpec
