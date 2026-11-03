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
    `h`, in the tree with leaves `cs`.

    `m` is the path's node at level `h+1`; the two values are its children. -/
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
    - **the claimed path** (`O.inputsAt c h`): opening `O`, going up from the claimed leaf `c`;
    - **the real path** (`realInputsAt cs O.index h`): in the tree with leaves `cs`, at the
      same position.
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
    - **the worlds** (`ws`): `ws j` is the world right after transaction `j - 1`, before
      `updatedValues j` (so `ws 0 = w0`), and `ws txs.length` is the final world;
    - **the balances and config before each transaction** (`updatedValues j`): their values
      after what happened outside `transact` since the previous transaction: SOL sent to the
      pool or to other accounts, other accounts spent from, admin changes to the config.
      `allowed`: Solana and the program allow it (`UpdatedValuesBetweenTransacts.Allowed`).
      `updatedValues 0` includes the part of any SOL sent to the pool before `initialize`
      that exceeds the pool's rent (`initialize` only tops the account up to its rent);
    - **each step is accepted** (`step`): transaction `j` is accepted (`transact`) from
      world `j` with `updatedValues j`, and leads to world `j + 1`.
    What happens after the last transaction is not part of the run.

    How the theorems use it: each quantifies over all runs from `initWorld params`, so it
    holds whatever transactions were submitted and whatever happened between them. (`w0`
    is a parameter only so some lemmas need fewer arguments.) A run is ghost data: the
    program doesn't store it; it exists only to state the theorems.

    Example. The order, for a run of two transactions:

        ws 0 = w0  (`start`)
          │  the balances and config become `updatedValues 0`
          ▼
        (ws 0).withUpdatedValues (updatedValues 0)
          │  step 0: transaction `txs[0]`, accepted by `transact`
          ▼
        ws 1
          │  the balances and config become `updatedValues 1`
          ▼
        (ws 1).withUpdatedValues (updatedValues 1)
          │  step 1: transaction `txs[1]`, accepted by `transact`
          ▼
        ws 2 = the final world -/
structure Run (w0 : World) where
  txs : List TxInputs
  ws : ℕ → World
  updatedValues : ℕ → UpdatedValuesBetweenTransacts
  start : ws 0 = w0
  allowed : ∀ j < txs.length, (updatedValues j).Allowed (ws j)
  step : ∀ j (h : j < txs.length),
    transact txs[j] ((ws j).withUpdatedValues (updatedValues j)) (ws (j+1))

/-- `r.donations j`: the SOL sent to the pool from outside just before transaction `j`.

    The pool's balance in `updatedValues j` minus its balance in `ws j`. The pool can only gain
    then (`allowed`), so the subtraction loses nothing. -/
def Run.donations {w0 : World} (r : Run w0) (j : ℕ) : ℕ :=
  (r.updatedValues j).balances (r.ws j).state.pool - (r.ws j).poolBalance

/-- `r.donated`: the SOL sent to the pool from outside during the run, summed over the
    gaps before each transaction. SOL sent before `initialize` counts only above the
    pool's rent (see `Run`). -/
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
  -- For all transactions in the run, if the proof is valid => relation S holds for witness for j
  ∀ j (h : j < r.txs.length), proofValid r.txs[j] → RelationS r.txs[j].pubInputs (wit j)

/-- `w.inNote i`: the note input `i` of witness `w` spends: amount, owner public key,
    blinding factor, token (mint). -/
def Witness.inNote (w : Witness) (i : Fin 2) : Note :=
  ⟨w.inAmt i, w.inPk i, w.inR i, w.mint⟩

/-- `w.outNote o`: the note output `o` of witness `w` creates: amount, owner public key,
    blinding factor, token (mint). -/
def Witness.outNote (w : Witness) (o : Fin 2) : Note :=
  ⟨w.outAmt o, w.outPk o, w.outR o, w.mint⟩

/-- `w.openedPos i`: the tree position that input `i` of `w` opens, i.e. the leaf index of that
    input's Merkle opening. -/
def Witness.openedPos (w : Witness) (i : Fin 2) : ℕ := (w.openings i).index.val

/-- `openedPos wit j i`: the tree position that input `i` of transaction `j` opens, i.e. the
    leaf index of that input's Merkle opening. For a non-zero input, the position of the
    note it spends; for a dummy (zero-amount) input, an arbitrary position. -/
def openedPos (wit : ℕ → Witness) (j : ℕ) (i : Fin 2) : ℕ := (wit j).openedPos i

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

/-- `GenuineInput wit w i bound`: input `i` of `w` spends a real note the spender is entitled
    to. One field per attack it rules out:
    - a made-up note: `inTree`;
    - someone else's note: `ownsNote`;
    - a real note for more than it holds: `knowsNote`.
    Whether the note was already spent is a separate question (G1b). -/
structure GenuineInput (wit : ℕ → Witness) (w : Witness) (i : Fin 2) (bound : ℕ) : Prop where
  /-- It opens one of the first `bound` leaves. -/
  inTree : w.openedPos i < bound
  /-- The spender holds the note's secret key: the public key of the note stored at this position
      is `H1` of the spender's secret key. -/
  ownsNote : (leafNote wit (w.openedPos i)).ownerPk = H1 (w.inSk i)
  /-- The spender states the stored note's real amount, blinding factor and mint. -/
  knowsNote :
    let storedNote := leafNote wit (w.openedPos i)
    storedNote.amount = w.inAmt i ∧ storedNote.blinding = w.inR i ∧ storedNote.mint = w.mint

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

/-- `DoubleSpendInputs w i w' i'`: input `i` of `w` and input `i'` of `w'` are both real spends of
    the same tree position. -/
abbrev DoubleSpendInputs (w : Witness) (i : Fin 2) (w' : Witness) (i' : Fin 2) : Prop :=
  -- both real spends (input amount not 0),
  w.inAmt i ≠ 0 ∧ w'.inAmt i' ≠ 0
  -- that open the same position in the tree
  ∧ w.openedPos i = w'.openedPos i'

/-- `DoubleSpend wit j i j' i'`: input `i` of transaction `j` and input `i'` of transaction
    `j'` are two different real spends of the same tree position. -/
def DoubleSpend (wit : ℕ → Witness) (j : ℕ) (i : Fin 2) (j' : ℕ) (i' : Fin 2) : Prop :=
  -- two different inputs (possibly of the same transaction),
  (j, i) ≠ (j', i') ∧ DoubleSpendInputs (wit j) i (wit j') i'

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
  let (c, pos, sign) := w.nullifierArgs i
  H3 c pos sign

/-- `NullifierCollision w i w' i'`: input `i` of `w` and input `i'` of `w'` reveal the same
    nullifier without being the same note at the same position. A nullifier is
    `H3 (commitment, position, signature)`, so this needs one of:
    - **different `H3` inputs** (`H3Collision`): the two triples differ but hash to the same
      nullifier;
    - **different notes, same commitment** (`H4Collision`): the two inputs' notes differ but
      have the same commitment. -/
def NullifierCollision (w : Witness) (i : Fin 2) (w' : Witness) (i' : Fin 2) : Prop :=
  H3Collision (w.nullifierArgs i) (w'.nullifierArgs i') ∨ H4Collision (w.inNote i) (w'.inNote i')

/-- `NullifierTakenByCollision r wit w`: an input of run `r` revealed the nullifier of an input of
    the owner's spend `w` first, through an `H3` collision, so the program rejects the spend.

    It takes a collision because of `inputNotUsedBefore`: no input of the run has that input's
    commitment at that position, so an equal nullifier must come from different hashed values.

    `wit`: the witnesses of the run's transactions. -/
def NullifierTakenByCollision {w0 : World} (r : Run w0) (wit : ℕ → Witness) (w : Witness) : Prop :=
  -- For some input `i` of `w`, there is an input `i'` of a transaction `j` of the run
  ∃ i, ∃ j, ∃ (hj : j < r.txs.length), ∃ i',
    -- that revealed the same nullifier as input `i` of `w`,
    r.txs[j].pubInputs.nullifiers i' = w.inNullifier i
    -- but from different values (commitment, position, signature):
    -- so an `H3` collision must have happened to make this possible
    ∧ H3Collision (w.nullifierArgs i) ((wit j).nullifierArgs i')


/-! ### The pieces of G3 (liveness) -/

/-- `RootIsPast r inputs k`: the spend's root is a real past root of `r`: the root of the
    tree after its first `k` leaves. -/
structure RootIsPast {w0 : World} (r : Run w0) (inputs : TxInputs) (k : ℕ) : Prop where
  /-- The spend uses the tree as it was after its first `k` leaves... -/
  isPrefix : k ≤ 2 * r.txs.length
  /-- ...and its root. -/
  isPrefixRoot : inputs.R = (foldAppend (r.firstLeaves k) initTree).root

/-- `TxWellFormed inputs pool`: the transaction's own fields are filled in correctly, and it
    carries a valid proof. Each field is the precondition of the same meaning in
    `transactPreconditions`. `pool`: the pool's address. -/
structure TxWellFormed (inputs : TxInputs) (pool : Pubkey) : Prop where
  /-- The proof verifies. -/
  validProof : proofValid inputs
  /-- The external data hashes to the value the proof commits to. -/
  externalData : externalDataBound inputs
  /-- The public amount is `extAmt - fee`. -/
  publicAmount : pubAmtConsistent inputs.extAmt inputs.f inputs.pubAmt
  /-- `extAmt` fits an `i64` and the fee a `u64`. -/
  amountRange : amountsInRange inputs.extAmt inputs.f
  /-- Each encrypted output is shorter than `2^32` bytes. -/
  encOutLength : encOutsFit inputs
  /-- The seven public inputs are sent as their canonical encodings. -/
  encodings : publicInputsEncoded inputs
  /-- The pool is not named where it would be paid. -/
  poolSeparate : poolIsSeparate inputs pool

/-- `InputUsedInRun r wit w i`: some input of the run has the same commitment at the same
    position as input `i` of `w`. -/
def InputUsedInRun {w0 : World} (r : Run w0) (wit : ℕ → Witness) (w : Witness) (i : Fin 2) : Prop :=
  ∃ j < r.txs.length, ∃ earlier,
    (wit j).inC earlier = w.inC i ∧ (wit j).openedPos earlier = w.openedPos i

/-- `HonestSpend r wit inputs witness k`: everything the owner controls: after run `r`, the owner
    builds `inputs` honestly from the secrets `witness`, spending notes they really can spend.

    Each input is a real note (`inAmt i ≠ 0`) or a dummy (`inAmt i = 0`).
    Real notes are `genuine` (G1a) and not double spent (`notDoubleSpend`, G1b);
    both must satisfy `inputNotUsedBefore`.
    The rest is the transaction: `root`, `circuit`, `wellFormed` and `signerCanPay`.

    `k`: the spend's root is the tree's root after its first `k` leaves. `wit`: the witnesses
    of the run's transactions. -/
structure HonestSpend {w0 : World} (r : Run w0) (wit : ℕ → Witness) (inputs : TxInputs)
    (witness : Witness) (k : ℕ) : Prop where
  /-- Each real note is genuine (G1a's notion), among the first `k` leaves. -/
  genuine : ∀ i, witness.inAmt i ≠ 0 → GenuineInput wit witness i k
  /-- The current spend's two inputs don't double spend a note (G1b's notion). -/
  notDoubleSpend : ¬ DoubleSpendInputs witness 0 witness 1
  /-- No input of this spend has been used before, so its nullifier is new, unless an `H3`
      collision occurs. -/
  inputNotUsedBefore : ∀ i, ¬ InputUsedInRun r wit witness i
  /-- The spend's root is a real past root. -/
  root : RootIsPast r inputs k
  /-- The owner's witness satisfies the circuit. -/
  circuit : RelationS inputs.pubInputs witness
  /-- The transaction's own fields are correct, and it carries a valid proof. -/
  wellFormed : TxWellFormed inputs r.final.state.pool
  /-- The signer's account can pay the rent for the two nullifier accounts and the deposit. -/
  signerCanPay : signerSolvent r.final.balances inputs.s inputs.extAmt r.final.nullifierRent

/-- `LimitsNotHit w inputs`: what can legitimately block the spend `inputs` in world `w`, and the
    owner can't ensure: an attacker or an admin can make these false.

    Attacker, by sending transactions or SOL: `inWindow`, `treeRoom` and `balancesFit`.
    Admin, by changing the config: `fee` and `depositLimit`. -/
structure LimitsNotHit (w : World) (inputs : TxInputs) : Prop where
  /-- The spend's root has not left the 100-slot root history yet. -/
  inWindow : inputs.R ∈ Set.range w.state.tree.history
  /-- The tree is not full. -/
  treeRoom : treeHasRoom w.state.tree
  /-- No balance a payment credits overflows a `u64` (unreachable in practice: 2^64
      lamports exceeds the total SOL supply). -/
  balancesFit : balancesFit inputs w
  /-- The fee is at least the configured rate, minus the fee error margin. -/
  fee : feeSufficient w.state.config inputs.extAmt inputs.f
  /-- A deposit does not exceed the configured maximum. -/
  depositLimit : depositWithinLimit w.state.config inputs.extAmt

/-- `CanBeAccepted inputs w`: the program accepts `inputs` in world `w`, with its own proof.

    The spec's `transact` holds from `w` to the world `transactEffects` computes. -/
def CanBeAccepted (inputs : TxInputs) (w : World) : Prop :=
  transact inputs w (transactEffects inputs w)

/-- `SpendBlockedByBreak r wit witness k`: an attacker blocked the owner's honest spend
    (`witness`, against the root of the first `k` leaves), which needs a hash break.

    To make the program reject the spend, the attacker must defeat one of its checks:
    - **drain the pool** (`BreakInSomeSpend`): to leave too little SOL for the owner's
      withdrawal, the attacker must withdraw value no note backs: forge a spend or spend a
      note twice (G1c);
    - **use up the owner's nullifier** (`NullifierTakenByCollision`): the program rejects a
      nullifier already used. To use it first, the attacker must reveal it from different
      arguments, i.e. find an `H3` collision;
    - **make the root `0`** (`H2ZeroPreimage`): the program rejects the root `0`. To make
      the tree's root `0`, the attacker must add leaves whose two top subtrees hash to `0`,
      i.e. find an `H2` preimage of `0`. -/
def SpendBlockedByBreak {w0 : World} (r : Run w0) (wit : ℕ → Witness) (witness : Witness) (k : ℕ) : Prop :=
  -- Drain pool by breaking spending
  BreakInSomeSpend r wit
  -- or, already use the nullifiers
  ∨ NullifierTakenByCollision r wit witness
  -- or the 2 last nodes hash together to obtain 0 for root
  ∨ H2ZeroPreimage (treeHash (r.firstLeaves k) 25 0, treeHash (r.firstLeaves k) 25 1)

end LeanSpec
