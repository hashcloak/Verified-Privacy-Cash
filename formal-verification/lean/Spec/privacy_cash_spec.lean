import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

--///////// Note: SOL ONLY. In Phase 2 we'll distinguish between SOL and SPL.

-- TODO review what has been translated so far. There are definitely errors in the translation still.

--/////////////////////////////////////////
-- Definitions
--/////////////////////////////////////////
def p: ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

-- Type aliases with `abbrev`
abbrev F := ZMod p
abbrev Pubkey := BitVec 256 -- Public key from Solana
abbrev Bits:= List Bool
abbrev Byte := BitVec 8
abbrev Bytes := List Byte

-- Abstract definition of the hashes we use
class PoseidonHashes where
  H1: F → F
  H2: F → F → F
  H3: F → F → F → F
  H4: F → F → F → F → F

class Sha where
  sha256: Bytes → Bytes

/-- Read bytes as a number, little-endian (byte 0 is least significant),
    as `Fr::from_le_bytes_mod_order` does. -/
def natOfLE (bs : Bytes) : ℕ := bs.foldr (fun b acc => b.toNat + 256 * acc) 0

-- open the namespaces defined by the class definition
open PoseidonHashes Sha
/-
Supply instances of PoseidonHashes and Sha

This makes sure we can just use H1, H2, sha256 etc.
https://lean-lang.org/doc/reference/4.26.0/Namespaces-and-Sections/#Lean___Parser___Command___variable
"Section variables are parameters that are automatically added to declarations that mention them."
-/
variable [PoseidonHashes] [Sha]

/-
Security properties are stated as "the property holds, OR a hash collision at specific
values determined by the theorem's hypotheses". We never assume collision-freeness
(false for H2–H4 and unprovable for H1), and we never write the break as
`∃ a b, …Collision a b` (always true, hence vacuous). Breaks are Prop-valued structures.
-/

/-- `a` and `b` are different inputs with the same `H1` output. -/
structure H1Collision (a b : F) : Prop where
  ne : a ≠ b
  eq : H1 a = H1 b -- TODO should we rename this?

/-- Two different argument tuples with the same `H4` output. -/
structure H4Collision (a b : F × F × F × F) : Prop where
  ne : a ≠ b
  eq : H4 a.1 a.2.1 a.2.2.1 a.2.2.2 = H4 b.1 b.2.1 b.2.2.1 b.2.2.2 -- TODO should we rename this?

/-- Two different byte strings whose little-endian, mod-`p` reduced `sha256` digests
    collide -- the actual hash used to bind external transaction data
    (`externalDataHash`) into the circuit's public inputs. A weaker (hence easier to
    obtain) break than a raw `sha256` collision, since it also holds when two distinct
    digests happen to agree mod `p`. -/
structure Sha256Collision (a b : Bytes) : Prop where
  ne : a ≠ b
  eq : (natOfLE (sha256 a) : F) = (natOfLE (sha256 b) : F)

-- Keys, commitments, nullifiers
def pubKey (sk: F): F := H1 sk
def commit (amt pk r mint: F): F := H4 amt pk r mint
def signature (sk c: F) (leafIndex: Fin (2^26)): F := H3 sk c leafIndex
def nullifier (c sign: F) (leafIndex: Fin (2^26)): F := H3 c leafIndex sign

-- If two commitments are equal, the (amount, pubkey, blinding, mint) tuples that
-- produced them are equal too OR a hash collision occurred
lemma commitment_determines_value_or_collision
  (amt pk r mint amt' pk' r' mint' : F)
  (h : commit amt pk r mint = commit amt' pk' r' mint')
  : (amt, pk, r, mint) = (amt', pk', r', mint')
    ∨ H4Collision (amt, pk, r, mint) (amt', pk', r', mint') := by
  by_cases heq : (amt, pk, r, mint) = (amt', pk', r', mint')
  · exact Or.inl heq
  · exact Or.inr ⟨heq, h⟩

-- Merkle trees
structure Opening where
  -- leaf index
  index: Fin (2^26)
  -- map from level i to sibling hash for level i. For 26 levels.
  -- easy to use; `siblings i` gives the hash on level i
  siblings: Fin 26 → F

-- Whether the accumulated hash for level i should be the right-side argument in hashing
-- `Nat.testBit n i` returns bit i of n as a Bool
def Opening.accIsRight (O: Opening) (i: Fin 26) : Bool := Nat.testBit O.index i

-- Calculate root for opening (Merkle proof)
def Opening.calcRoot (O: Opening) (leaf: F) : F :=
  Fin.foldl 26 (fun acc i => if (O.accIsRight i) then H2 (O.siblings i) acc else H2 acc (O.siblings i)) (leaf)

-- The opening is deemed valid if the actual root equals the root given by the opening
def Opening.Valid (O: Opening) (leaf R: F): Prop := calcRoot O leaf = R

-- Z_i's; zero hashes. The default state of the Merkle tree with all leaves equal to 0.
def Z: ℕ → F
  | 0 => 0 -- Leaves are 0
  | i+1 => H2 (Z i) (Z i) -- Hash each next level

-- ZKP related

structure PubInputs where
  R: F
  pubAmt: F
  extDataHash: F
  nullifiers: Fin 2 → F
  outCommitments: Fin 2 → F

structure Witness where
  mint: F
  -- For all (2) inputs
  inAmt: Fin 2 → F -- input amount
  inSk: Fin 2 → F -- private key
  inR: Fin 2 → F -- blinding factor
  openings: Fin 2 → Opening -- merkle proof
  -- For all (2) outputs
  outAmt: Fin 2 → F -- output amount
  outPk: Fin 2 → F -- output public key
  outR: Fin 2 → F -- output blinding factor

-- Derived values
def Witness.inPk (w: Witness) (i: Fin 2): F := H1 (w.inSk i)
def Witness.inC (w: Witness) (i: Fin 2) : F := commit (w.inAmt i) (w.inPk i) (w.inR i) w.mint
def Witness.sign (w: Witness) (i: Fin 2): F := signature (w.inSk i) (w.inC i) (w.openings i).index

/-
Relation S
  In a structure so the separate constraints are easy to extract/name
  a term (h: RelationS pubInputs witness) would have to provide proofs for all constraints
  However, we'll mainly use it as a given and then use specific properties
-/
structure RelationS (pubInputs: PubInputs) (w: Witness) : Prop where
  -- Because of Fin 2 usage, range of j or i is deduced automatically
  outputCommitmentIntegrity: ∀ j,(pubInputs.outCommitments j) = commit (w.outAmt j) (w.outPk j) (w.outR j) (w.mint)
  nullifierCorrectness: ∀ i, pubInputs.nullifiers i = nullifier (w.inC i) (w.sign i) (w.openings i).index
  noDuplicateNullifiers: pubInputs.nullifiers 0 ≠ pubInputs.nullifiers 1
  correctOpenings: ∀ i ∈ {i | (w.inAmt i) ≠ 0}, (w.openings i).Valid (w.inC i) pubInputs.R
  amountConservation: (w.inAmt 0) + (w.inAmt 1) + pubInputs.pubAmt = (w.outAmt 0) + (w.outAmt 1)
  -- The check is not needed on the input amounts, because they were checked when deposited into the pool
  -- and because of note_value_consistency property, we know the value hasn't changed
  outputRangeChecks: ∀ j, (w.outAmt j).val < 2^248

/-
In math language:
Let G_1, G_2, G_T be types
G_1 is an additive commutative group with scalar multiplication
G_2 is an additive commutative group with scalar multiplication
G_T is an additive commutative group

For Lean:
Let Lean assume there is an AddCommGroup G1 instance available

(We don't have to provide the actual types, but can use the abstraction)
-/
opaque G1: Type
opaque G2: Type
opaque GT: Type
variable
  [AddCommGroup G1] [Module F G1]
  [AddCommGroup G2] [Module F G2]
  [CommGroup GT]

-- Define of the pairing property only what's needed for the Groth16 verification
class Pairing where
  -- Pairing operation
  e: G1 → G2 → GT
  -- Bilinearity of e
  e_smul_left: ∀ (s: F) (a: G1) (b: G2), e (s • a) b = (e a b) ^ s.val
  e_smul_right: ∀ (s: F) (a: G1) (b: G2), e a (s • b) = (e a b) ^ s.val

variable [Pairing]

namespace Groth16

structure Proof where
  A: G1
  B: G2
  C: G1

structure VerificationKey where
  α: G1
  β: G2
  γ: G2
  δ: G2
  IC: Fin 8 → G1


def toVector (x: PubInputs): Fin 7 → F :=
    ![x.R, x.pubAmt, x.extDataHash, x.nullifiers 0, x.nullifiers
  1, x.outCommitments 0, x.outCommitments 1]

-- Groth16 verification
-- e(A, B) = e(α, β) · e(vk_x, γ) · e(C, δ)
-- where vk_x = IC[0] + Σ x_i · IC[i+1]
def verify
    (vk: VerificationKey)
    (π: Proof)
    (x: PubInputs): Prop :=
    let pubInputsVec := toVector x
    -- For scalar multiplication (•) \bu or \smul
    let vkX : G1 := vk.IC 0 + ∑ i : Fin 7, (pubInputsVec i) • vk.IC i.succ
    Pairing.e π.A π.B = Pairing.e vk.α vk.β * Pairing.e vkX vk.γ * Pairing.e π.C vk.δ

/-- Two different public-input vectors whose `vk`-weighted `IC` combinations pair
    identically against `γ` -- the break needed to defeat binding of `vk` to its public
    inputs. Stated at the `GT` level, not `G1`, since concluding `G1`-equality would need
    pairing non-degeneracy, an assumption `Pairing` doesn't make. -/
-- TODO we could also add the definition of non-degeneracy to pairing and then this would be a discrete log break
structure ICRelation (vk : VerificationKey) (x x' : PubInputs) : Prop where
  ne : x ≠ x'
  eq : Pairing.e (vk.IC 0 + ∑ i : Fin 7, (toVector x i) • vk.IC i.succ) vk.γ
     = Pairing.e (vk.IC 0 + ∑ i : Fin 7, (toVector x' i) • vk.IC i.succ) vk.γ

end Groth16

class Deployment where
  vk: Groth16.VerificationKey -- a fixed circuit
  -- We assume soundness & completeness of Groth16
  -- Unlike the hash primitives, no "OR here's the break" fallback: real soundness is
  -- computational (fails if the trusted setup's toxic waste leaked), but reducing to
  -- that would mean mechanizing Groth16's own security proof, out of scope here --
  -- soundness is imported as a trusted primitive, not re-derived.
  soundness: ∀ (π: Groth16.Proof) x, Groth16.verify vk π x → ∃ w, RelationS x w
  -- Dual of `soundness`, needed for invariant 10. Not an idealization like soundness
  -- is: Groth16 has *perfect* completeness, a proven property of the construction.
  completeness: ∀ x w, RelationS x w → ∃ π, Groth16.verify vk π x

variable [Deployment]

-- Configurations for the privacy-cash contract
structure config where
  authority: Pubkey -- the authority that can change the config
  depositFeeRate: ℕ -- in basis points, e.g. 25 = 0.25%, default = 0
  withdrawalFeeRate: ℕ -- in basis points, default = 0.25%
  feeMarginError: ℕ -- in basis points, default = 500 (5% tolerance)
  -- NOTE: In solana code the max deposit limit in declared in the Merkle Tree but we have kept in here.
  -- TODO should we move this
  maxDepositLimit: ℕ -- maximum deposit amount in lamports

--/////////////////////////////////////////
-- (3) State
--/////////////////////////////////////////
structure Tree where
  nextIndex: ℕ
  subtrees: Fin 26 → F -- For each level, a hash
  root: F
  history: Fin 100 → F
  rootIndex: Fin 100

structure State where
  tree: Tree
  nullifiers: Finset F
  solBalance: ℕ
  config: config

-- Needed: `balances` is how deposits/withdrawals/fees actually move real SOL between
-- accounts (`transferEffects`, `transactEffects`), how `AgreesOnProgramEffects.payees`
-- states the recipient/fee-recipient are paid, and how `signerSolvent` checks a
-- depositor can cover their deposit. Without it there'd be nothing to state those over.
structure World where
  state: State
  balances: Pubkey → ℕ -- balances of (public) Solana accounts in lamports
  -- the minimum lamport balance an account must have to keep existing without paying rent
  rentExemptMin: ℕ

--/////////////////////////////////////////
-- (4) Operations
--/////////////////////////////////////////

-- Append a single commitment to the merkle tree
-- Doc ref https://privacy-cash-privacy-cash.mintlify.app/concepts/merkle-trees#appending-commitments
def appendEffects(c: F) (oldTree: Tree): Tree :=
  let current := c
  let index := oldTree.nextIndex
  let newRootIndex := oldTree.rootIndex +1
  let (newRoot, newSubtrees) :=
  -- Update the complete subtrees array and output the new root by folding.
  -- Fold left taking accumulator (current hash and subtrees values) and index (height)
  Fin.foldl 26 (fun (current, subtrees) height =>
      if Nat.testBit index height.val then
        -- If the index bit is odd, the accumulator goes on the right.
        (H2 (subtrees height) current, subtrees)
        else
        /-
        If the index bit is even, the accumulator goes on the left.

        Left siblings are stored, thus the subtrees gets updated.
        Function.update f i v will update function f for point i with value v
        -/
        (H2 current (Z height.val), Function.update subtrees height current)
    ) (current, oldTree.subtrees)
  {
    nextIndex := index +1
    subtrees := newSubtrees
    root := newRoot
    history := Function.update oldTree.history newRootIndex newRoot
    rootIndex := newRootIndex
  }

/-- The tree obtained by appending a sequence of commitments, in order, to `t0`. -/
def foldAppend (cs: List F) (t0: Tree): Tree :=
  cs.foldl (fun t c => appendEffects c t) t0

structure TxInputs where
  R: F -- Merkle root
  pubAmt: F -- public amount
  extDataHash: F -- external data hash
  k0: F -- input nullifier 0
  k1: F -- input nullifier 1
  outC0: F -- output commitment 0
  outC1: F -- output commitment 1
  extAmt: ℤ -- external amount
  f: ℕ -- fee
  s: Pubkey -- signer
  A : Pubkey -- recipient address
  t : Pubkey -- fee recipient
  encOut0: Bytes -- encrypted output 0
  encOut1: Bytes -- encrypted output 1
  π: Groth16.Proof -- Groth16 proof for relation S
  mintAddr: Pubkey -- token type

/-- The `PubInputs` record that `inputs` should produce a valid Groth16 proof for. -/
def TxInputs.pubInputs (inputs : TxInputs) : PubInputs :=
  { R := inputs.R, pubAmt := inputs.pubAmt, extDataHash := inputs.extDataHash,
    nullifiers := ![inputs.k0, inputs.k1], outCommitments := ![inputs.outC0, inputs.outC1] }

-- Borsh serialization (for the external data hash binding)
def natToBytesLE (width n: ℕ ): Bytes :=
  (List.range width).map (fun i => BitVec.ofNat 8 (n >>> (8 * i)))

def u32LE (n: ℕ): Bytes := natToBytesLE 4 n
def u64LE (n: ℕ): Bytes := natToBytesLE 8 n
def i64LE (n: ℤ): Bytes := natToBytesLE 8 (n %(2^64 : ℤ)).toNat
def PubkeyToBytes (pk: Pubkey): Bytes := natToBytesLE 32 pk.toNat
def vecU8 (bytes: Bytes): Bytes := u32LE bytes.length ++ bytes

def serealizeExternalData (inputs: TxInputs): Bytes :=
  PubkeyToBytes inputs.A ++ i64LE inputs.extAmt ++ vecU8 inputs.encOut0 ++ vecU8 inputs.encOut1 ++ u64LE inputs.f ++ PubkeyToBytes inputs.t ++ PubkeyToBytes inputs.mintAddr

def externalDataHash (inputs : TxInputs) : F :=
  (natOfLE (sha256 (serealizeExternalData inputs)) : F)

/- The actual moving of funds (note that this does not pay fees)
  **Transfer**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#universal-joinsplit-transactions)):
    - (deposit) if $extAmt>0;$ SOL balance' = SOL balance $+ extAmt$ and $balances(s)' = balances(s) - extAmt$
    - (withdrawal) if $extAmt<0;$ SOL balance' = SOL balance $- |extAmt|$ and $balances(A)' = balances(A) + |extAmt|$
    - (transfer) if $extAmt=0;$ no changes to balances
-/
def transferEffects (inputs: TxInputs) (oldWorld: World): World :=
  -- If the extAmt = 0, nothing changes. Otherwise return an updated version of the world.
  if inputs.extAmt = 0 then oldWorld else
    let extAmtAbs := Int.natAbs inputs.extAmt
    { oldWorld with
      state := {
        oldWorld.state with
        solBalance :=
          -- For a deposit, increase the solBalance in the state. For a withdrawal, lower
          -- it. No guard needed here: withdrawal underflow is exactly what
          -- `poolSolvency` rules out (see `sol_balance_correctness`), and `ℕ` doesn't
          -- overflow in this idealized model, matching the rest of the file's u64
          -- abstraction (real overflow is out of scope, see the top-of-file TODO).
          if inputs.extAmt > 0 then oldWorld.state.solBalance + extAmtAbs
          else oldWorld.state.solBalance - extAmtAbs
      }
      balances :=  if inputs.extAmt > 0 then
        -- For a deposit, decrease the signer's SOL balance (in Solana account). No
        -- guard needed here either: underflow is exactly what `signerSolvent` rules out
        -- (mirrors `poolSolvent`; `signer_lamports.checked_sub` fails the real
        -- transaction outright if the signer can't cover the deposit).
        Function.update oldWorld.balances inputs.s ((oldWorld.balances inputs.s) - extAmtAbs)
        else
        -- For a withdrawal, increase the SOL balance of the recipient (in Solana account)
        Function.update oldWorld.balances inputs.A ((oldWorld.balances inputs.A) + extAmtAbs)
    }

-- Returns a new World after updating all necessary elements according to the txInputs
def transactEffects (inputs: TxInputs)(oldWorld: World): World :=
  -- Move the actual funds. In a separate function for clarity
  let worldAfterTransfers := transferEffects inputs oldWorld
  { worldAfterTransfers with
    state:= { worldAfterTransfers.state with
      -- Append outC0, then append outC1.
      -- This insert the output commitments & updates the Merkle root
      tree:= appendEffects inputs.outC1 (appendEffects inputs.outC0 worldAfterTransfers.state.tree)
      -- Add nullifiers to the state.
      nullifiers := worldAfterTransfers.state.nullifiers ∪ {inputs.k0, inputs.k1}
      -- The fee leaves the pool's SOL balance (paid out to the fee recipient below).
      solBalance := worldAfterTransfers.state.solBalance - inputs.f
    }
    -- Add the fee to the fee recipient's balance
    balances := Function.update worldAfterTransfers.balances inputs.t ((worldAfterTransfers.balances inputs.t) + inputs.f)
  }

--/////////////////////////////////////////
-- Preconditions, one named condition each.
-- Each is stated over the plain values it depends on, so the code-side theorem for
-- the corresponding Rust check can refer to it directly.
--/////////////////////////////////////////

-- R is a non-zero root in the tree's root history.
def rootKnown (T: Tree) (R: F): Prop :=
  R ∈ Set.range T.history ∧ R ≠ 0

-- The external data (recipient, amounts, fee, encrypted outputs, mint) hashes to the
-- value the proof commits to.
def externalDataBound (inputs: TxInputs): Prop :=
  externalDataHash inputs = inputs.extDataHash

-- The fee is at least the configured rate, minus the allowed error margin.
def feeSufficient (cfg: config) (extAmt: ℤ) (f: ℕ): Prop :=
  let feeErrorMargin := cfg.feeMarginError
  let feeRate := if extAmt > 0 then cfg.depositFeeRate else cfg.withdrawalFeeRate
  let expectedFee := (extAmt.natAbs * feeRate) / 10000
  let minAcceptableFee := (expectedFee * (10000 - feeErrorMargin)) / 10000
  f ≥ minAcceptableFee

-- The public amount the proof commits to is extAmt - fee, and extAmt is in range.
def pubAmtConsistent (extAmt: ℤ) (f: ℕ) (pubAmt: F): Prop :=
  -- reference i64::MIN https://doc.rust-lang.org/std/i64/constant.MIN.html
  extAmt ≠ -9_223_372_036_854_775_808 ∧
  (extAmt > 0 → extAmt > f) ∧
  pubAmt = (extAmt: F) - f

-- The Groth16 proof verifies for the deployed key and these public inputs.
def proofValid (inputs: TxInputs): Prop :=
  Groth16.verify Deployment.vk inputs.π inputs.pubInputs

-- Neither input nullifier has been spent before.
def nullifiersFresh (spent: Finset F) (k0 k1: F): Prop :=
  k0 ∉ spent ∧ k1 ∉ spent

-- The two input nullifiers differ. Enforced by the circuit (`noDuplicateNullifiers`),
-- not checked by the program itself.
def nullifiersDistinct (k0 k1: F): Prop :=
  k0 ≠ k1

-- A deposit does not exceed the configured maximum.
def depositWithinLimit (cfg: config) (extAmt: ℤ): Prop :=
  extAmt > 0 → extAmt ≤ cfg.maxDepositLimit

-- The pool can pay out the withdrawal and the fee and still keep its rent reserve.
def poolSolvent (solBalance rentExemptMin: ℕ) (extAmt: ℤ) (f: ℕ): Prop :=
  (extAmt < 0 → solBalance ≥ |extAmt| + f + rentExemptMin) ∧
  (extAmt ≥ 0 ∧ f > 0 → solBalance ≥ f + rentExemptMin)

-- The signer has enough SOL to cover a deposit. Mirrors `poolSolvent` for the other
-- direction: `signer_lamports.checked_sub(deposit_amount)` (lib.rs) fails the
-- transaction outright if this doesn't hold, it isn't a silent underflow on-chain.
def signerSolvent (balances: Pubkey → ℕ) (s: Pubkey) (extAmt: ℤ): Prop :=
  extAmt > 0 → balances s ≥ extAmt.natAbs

-- There is room in the tree for the two output commitments.
def treeHasRoom (T: Tree): Prop :=
  T.nextIndex < (2^26-2)

structure transactPreconditions
  (inputs: TxInputs)
  (oldWorld: World): Prop where
  knownRoot: rootKnown oldWorld.state.tree inputs.R
  externalDataBinding: externalDataBound inputs
  minimumFee: feeSufficient oldWorld.state.config inputs.extAmt inputs.f
  pubAmtConsistency: pubAmtConsistent inputs.extAmt inputs.f inputs.pubAmt
  validZKP: proofValid inputs
  newNullifiers: nullifiersFresh oldWorld.state.nullifiers inputs.k0 inputs.k1
  distinctNullifiers: nullifiersDistinct inputs.k0 inputs.k1
  depositLimit: depositWithinLimit oldWorld.state.config inputs.extAmt
  poolSolvency: poolSolvent oldWorld.state.solBalance oldWorld.rentExemptMin inputs.extAmt inputs.f
  signerSolvency: signerSolvent oldWorld.balances inputs.s inputs.extAmt
  -- The 2 output commitments are added to the tree; make sure there is space for both
  treeNotFull: treeHasRoom oldWorld.state.tree

/-- Temporary, field-by-field stand-in for `actual = predicted` (see "Future work"
    note below `transact`). TODO(security gap): `payees` excludes the signer's own
    balance entirely, so nothing here verifies that a deposit actually debited the
    signer — decide how to close this before relying on `transact`. -/
structure AgreesOnProgramEffects (inputs : TxInputs) (predicted actual : World) : Prop where
  tree          : actual.state.tree = predicted.state.tree
  nullifiers    : actual.state.nullifiers = predicted.state.nullifiers
  solBalance    : actual.state.solBalance = predicted.state.solBalance
  config        : actual.state.config = predicted.state.config
  rentExemptMin : actual.rentExemptMin = predicted.rentExemptMin
  payees : ∀ k, (k = inputs.A ∨ k = inputs.t) → k ≠ inputs.s →
    actual.balances k = predicted.balances k

/-
`transact` holds when a transaction from `oldWorld` to `newWorld` is allowed and has
the effects the program is responsible for: the preconditions hold in `oldWorld`, and
`newWorld` agrees with `transactEffects inputs oldWorld` per `AgreesOnProgramEffects`
(see its doc comment for why this isn't exact equality).

`transact` also does not state that all other balances are unchanged. No theorem here
depends on it; the code-side connection theorem states it separately.
-/
def transact
  (inputs: TxInputs)
  (oldWorld: World)
  (newWorld: World)
  : Prop :=
  -- Preconditions hold AND
  (transactPreconditions inputs oldWorld) ∧
  -- The effects have been executed correctly, i.e. newWorld agrees with transactEffects on the parts the program controls
  AgreesOnProgramEffects inputs (transactEffects inputs oldWorld) newWorld

-- Future work: model rent for the nullifier accounts and network fees in
-- `transactEffects`. Then `transact` can require `newWorld = transactEffects inputs oldWorld`
-- again, which also states that no other balance changed. Existing theorems carry over,
-- since equality implies every comparison made here.

--/////////////////////////////////////////
-- (5) Invariants
--/////////////////////////////////////////
-- Properties that hold for all reachable states.

-- HELPER DEFINITIONS

def initTree : Tree := {
  nextIndex := 0
  subtrees := fun i => Z i.val
  root:= Z 26
  -- Matches `MerkleTree::initialize` (merkle_tree.rs): only slot 0 is set to the
  -- zero-tree root; the rest are left at Solana's zero-initialized account bytes, i.e.
  -- the field element `0`, never `Z 26`. `is_known_root` explicitly rejects `root = 0`
  -- first, precisely because these untouched slots must not be mistaken for real roots.
  history := fun i => if i = 0 then Z 26 else 0
  rootIndex := 0
}

def initWorld(config: config)(balances: Pubkey → ℕ)(rentExemptMin: ℕ) : World := {
  state := {
    tree := initTree
    nullifiers := ∅
    solBalance := 0
    config := config
  }
  balances := balances
  rentExemptMin := rentExemptMin
}

-- A claim about a pair of worlds; can we go from w1 to w2?
--   This lets us reason about "in any number of steps"
inductive ReachableWorld: World → World → Prop where
  -- No transactions; true for any world
 | noStep(w1: World): ReachableWorld w1 w1
 -- Given a reachable pair w1, w2 and
 -- a proof that transact succeeds from w2 to w3,
 -- Then obtain proof that w3 is reachable from w1
 | extend{w1 w2 w3: World}(txInputs: TxInputs):
      ReachableWorld w1 w2 →
      transact txInputs w2 w3 →
       ReachableWorld w1 w3

-- 1. Set of nullifiers can only grow.

-- Proof for a single step executing transact.
-- Given:
  -- vk for the circuit
  -- an old_world
  -- txInputs
  -- a new_world
-- When: transact succeeds, producing a new_world
-- Then: world.nullifiers subset new_world.nullifier
lemma nullifier_set_monotonicity_step
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h: transact inputs oldWorld newWorld)
  : oldWorld.state.nullifiers ⊂ newWorld.state.nullifiers := by
  -- Direct proof: unfold `transact`, then hand back `inputs.k0` as the witness element that's
  -- in `newWorld` but not `oldWorld`.
  -- `transact` gives us that `newWorld` is exactly `transactEffects inputs oldWorld`, and its
  -- preconditions guarantee `k0` is a fresh nullifier, absent from `oldWorld`.
  obtain ⟨hpre, hagree⟩ := h
  have hk0New : inputs.k0 ∉ oldWorld.state.nullifiers := hpre.newNullifiers.1
  -- the new nullifier set is the one `transactEffects` predicts
  rw [hagree.nullifiers]
  simp only [transactEffects, transferEffects]
  split_ifs <;>
    exact (Finset.ssubset_iff_of_subset Finset.subset_union_left).mpr
      ⟨inputs.k0, Finset.mem_union_right _ (Finset.mem_insert_self _ _), hk0New⟩

-- General proof by induction for Reachable Worlds
-- `ReachableWorld` includes the zero-step case (`noStep`, where w1 = w2), so the strongest
-- claim that holds in general is non-strict monotonicity (⊆), not a proper subset (⊂).
theorem nullifier_set_monotonicity
  (w1 w2: World)
  (h: ReachableWorld w1 w2)
  : w1.state.nullifiers ⊆ w2.state.nullifiers := by
  -- Induction proof on `ReachableWorld`
  induction h with
  -- For same world, it holds trivially
  | noStep => exact Finset.Subset.refl _
  -- For the induction step, we use the property that each transact step strictly grows the
  -- set of nullifiers
  -- ih = induction hypothesis
  | extend inputs _h transact_proof ih =>
    -- `ih : w1.state.nullifiers ⊆ w2.state.nullifiers` (from the reachability so far), and
    -- the single `transact` step from w2 to w3 strictly grows the nullifier set
    -- (nullifier_set_monotonicity_step). Chain the two, then weaken the resulting ⊂ back to
    -- ⊆ to match this theorem's (necessarily non-strict) conclusion.
    exact (ih.trans_ssubset (nullifier_set_monotonicity_step _ _ inputs transact_proof)).subset

-- 2. No double spend
-- No nullifier reuse
-- No note reuse
-- This is within tx and across txs (with any nr of txs in between)
-- Level 1: nullifier level
-- Level 2: note level (the same note leads to the same nullifier)
-- Level 3: commitment level (this uses hash collision resistance)
-- TODO: a spend claiming a different leaf index isn't ruled out yet see the
-- "GAP: Merkle position binding" note after invariant 7.

-- 2a. After `transact` has been executed with a nullifier
-- A second `transact` with the same nullifier should not be possible
-- (with any nr of txs in between)
theorem no_nullifier_reuse_possible_across_txs
  (w1 w2 w2' w3: World)
  (nullifierToReuse: F)
  (txInputs1 txInputs2: TxInputs)
  (h1: (nullifierToReuse = txInputs1.k0 ∨ nullifierToReuse = txInputs1.k1) ∧ (nullifierToReuse = txInputs2.k0 ∨ nullifierToReuse = txInputs2.k1))
  (h2: transact txInputs1 w1 w2)
  -- Zero or more further transactions (arbitrary inputs each) between `txInputs1` and
  -- `txInputs2` -- see `ReachableWorld`'s `noStep`/`extend` constructors. The zero-step case
  -- (`w2' = w2`) covers an immediate replay of `txInputs1` with no intervening transactions.
  (h3: ReachableWorld w2 w2')
  : ¬ transact txInputs2 w2' w3 := by
  -- Proof by contradiction: if such a nullifier exists, it is both present & excluded from the set of nullifiers ↯
  intro h4
  obtain ⟨_, heff2⟩ := h2
  obtain ⟨hpre4, _⟩ := h4
  -- `nullifierToReuse` lands in `w2`'s nullifier set, since it equals one of `txInputs1`'s
  -- input nullifiers, which `transactEffects` adds.
  have hmemW2 : nullifierToReuse ∈ w2.state.nullifiers := by
    rw [heff2.nullifiers]
    simp only [transactEffects, transferEffects]
    rcases h1.1 with h | h <;> split_ifs <;> simp [h]
  -- `nullifier_set_monotonicity` carries that membership across any number of further txs.
  have hmemW2' : nullifierToReuse ∈ w2'.state.nullifiers :=
    nullifier_set_monotonicity w2 w2' h3 hmemW2
  -- But `txInputs2`'s `newNullifiers` precondition requires both its input nullifiers to be
  -- absent from `w2'`, and `nullifierToReuse` equals one of them.
  have hnotmemW2' : nullifierToReuse ∉ w2'.state.nullifiers := by
    rcases h1.2 with h | h
    · exact h ▸ hpre4.newNullifiers.1
    · exact h ▸ hpre4.newNullifiers.2
  -- Contradiction: `nullifierToReuse` is both present and absent from `w2'.state.nullifiers`.
  exact absurd hmemW2' hnotmemW2'

-- Corollary of 2a: given a nullifier equality between `txInputs1`'s input `i` and
-- `txInputs2`'s input `i'`, the second transact can't happen either. Reused by 2c and 2e.
lemma no_reuse_across_txs_from_nullifier_eq
  (w1 w2 w2' w3: World)
  (txInputs1 txInputs2: TxInputs)
  (i i': Fin 2)
  (hNullEq: txInputs1.pubInputs.nullifiers i = txInputs2.pubInputs.nullifiers i')
  (h4: transact txInputs1 w1 w2)
  (h5: ReachableWorld w2 w2')
  : ¬ transact txInputs2 w2' w3 := by
  apply no_nullifier_reuse_possible_across_txs w1 w2 w2' w3 (txInputs1.pubInputs.nullifiers i)
    txInputs1 txInputs2 ⟨?_, ?_⟩ h4 h5
  · fin_cases i <;> simp [TxInputs.pubInputs]
  · rw [hNullEq]; fin_cases i' <;> simp [TxInputs.pubInputs]

-- 2b. If txInputs has two equal nullifiers for inputs, transact shouldn't be possible.
theorem no_nullifier_reuse_possible_within_txs
  (w1 w2: World)
  (nullifierToReuse: F)
  (txInputs: TxInputs)
  (h1: nullifierToReuse = txInputs.k0 ∧ nullifierToReuse = txInputs.k1):
  ¬ transact txInputs w1 w2 := by
  -- Proof by contradiction: like above
  intro h2
  obtain ⟨hpre, _⟩ := h2
  -- `distinctNullifiers` requires k0 ≠ k1; but h1 identifies both with `nullifierToReuse`.
  have heq : txInputs.k0 = txInputs.k1 := h1.1.symm.trans h1.2
  exact absurd heq hpre.distinctNullifiers

-- HELPER (level 2)
-- What is the note? https://privacy-cash-privacy-cash.mintlify.app/concepts/commitments-and-nullifiers#nullifiers
-- amount, pubkey (from privkey), blinding, mint
--  plus: leafIndex
--  plus, but redundant: signature over commitment. This reuses privkey, commitment and leafIndex
-- So a note is uniquely defined by: amount, pubkey (from privkey), blinding, mint, leafIndex of Merkle Proof
-- The commitment only depends on pubkey, but the nullifier's signature is built straight from
-- the privkey, not the pubkey. pk = H1(sk) is one-directional: unless H1 is collision-free
-- (not assumed), two different privkeys could share a pubkey. So matching pubkeys wouldn't
-- guarantee matching signatures. h3 compares inSk directly to avoid relying on that.
lemma same_note_same_nullifier
  (witness1 witness2: Witness)
  (pubInput1 pubInput2: PubInputs)
  (h1: RelationS pubInput1 witness1)
  (h2: RelationS pubInput2 witness2)
  (i i': Fin 2)
  (h3: witness1.inAmt i = witness2.inAmt i'
    ∧ witness1.inSk i = witness2.inSk i'
    ∧ witness1.inR i = witness2.inR i'
    ∧ witness1.mint = witness2.mint
    ∧ (witness1.openings i).index = (witness2.openings i').index)
  : pubInput1.nullifiers i = pubInput2.nullifiers i' := by
  obtain ⟨hAmt, hSk, hR, hMint, hIdx⟩ := h3
  have hPk : witness1.inPk i = witness2.inPk i' := by
    simp only [Witness.inPk, hSk]
  have hC : witness1.inC i = witness2.inC i' := by
    simp only [Witness.inC, commit, hAmt, hPk, hR, hMint]
  have hSign : witness1.sign i = witness2.sign i' := by
    simp only [Witness.sign, signature, hSk, hC, hIdx]
  rw [h1.nullifierCorrectness i, h2.nullifierCorrectness i']
  simp only [nullifier, hC, hIdx, hSign]

-- 2c. No same-note reuse across txs. `witness1` and `witness2` are the witnesses used for
-- `txInputs1` and `txInputs2` (via `RelationS`). If `witness1`'s input `i` is the same note as
-- `witness2`'s input `i'` (same amount, secret key, blinding, mint, and leaf index of opening)
-- spending it again in a second transfer is not possible, with any number of txs in between.
theorem no_note_reuse_possible_across_txs
  (w1 w2 w2' w3: World)
  (txInputs1 txInputs2: TxInputs)
  (witness1 witness2: Witness)
  (hRel1: RelationS txInputs1.pubInputs witness1)
  (hRel2: RelationS txInputs2.pubInputs witness2)
  (i i': Fin 2)
  (h3: witness1.inAmt i = witness2.inAmt i'
    ∧ witness1.inSk i = witness2.inSk i'
    ∧ witness1.inR i = witness2.inR i'
    ∧ witness1.mint = witness2.mint
    ∧ (witness1.openings i).index = (witness2.openings i').index)
  (h4: transact txInputs1 w1 w2)
  (h5: ReachableWorld w2 w2') -- Any amount of txs in between after the first txs
  : ¬ transact txInputs2 w2' w3 := by
  -- Reduction proof: same note gives same nullifier, then apply theorem 2a via the corollary.
  have hNullEq := same_note_same_nullifier witness1 witness2 txInputs1.pubInputs txInputs2.pubInputs
    hRel1 hRel2 i i' h3
  exact no_reuse_across_txs_from_nullifier_eq w1 w2 w2' w3 txInputs1 txInputs2 i i' hNullEq h4 h5

-- 2d. A single txs can't spend the same note for both inputs:
-- no valid witness exists for it.
theorem no_note_reuse_possible_within_txs
  (txInputs: TxInputs)
  (witness: Witness)
  (h1: witness.inAmt 0 = witness.inAmt 1
    ∧ witness.inSk 0 = witness.inSk 1
    ∧ witness.inR 0 = witness.inR 1
    -- mint is defined per witness, so can't be compared
    ∧ (witness.openings 0).index = (witness.openings 1).index)
  : ¬ RelationS txInputs.pubInputs witness := by
  -- Proof by contradiction: if such a witness exists, they have the same nullifier,
  -- contradicting `noDuplicateNullifiers` in RelationS ↯
  intro hRel
  have hNullEq := same_note_same_nullifier witness witness txInputs.pubInputs txInputs.pubInputs
    hRel hRel 0 1 ⟨h1.1, h1.2.1, h1.2.2.1, rfl, h1.2.2.2⟩
  exact hRel.noDuplicateNullifiers hNullEq

-- HELPER (level 3)
-- The same commitment at the same leaf index, possibly opened with different values,
-- gives the same nullifier, unless the two witnesses exhibit an H1 collision on their
-- private keys or an H4 collision on their commitment openings.
-- Uses `same_note_same_nullifier` in the case where all values agree.
lemma same_commitment_same_nullifier_or_collision
  (witness1 witness2: Witness)
  (pubInput1 pubInput2: PubInputs)
  (h1: RelationS pubInput1 witness1)
  (h2: RelationS pubInput2 witness2)
  (i i': Fin 2)
  (sameIndex: (witness1.openings i).index = (witness2.openings i').index)
  (sameCommitment: witness1.inC i = witness2.inC i')
  : pubInput1.nullifiers i = pubInput2.nullifiers i'
    ∨ H1Collision (witness1.inSk i) (witness2.inSk i')
    ∨ H4Collision (witness1.inAmt i, witness1.inPk i, witness1.inR i, witness1.mint)
                  (witness2.inAmt i', witness2.inPk i', witness2.inR i', witness2.mint) := by
  have hCommitEq : commit (witness1.inAmt i) (witness1.inPk i) (witness1.inR i) witness1.mint
      = commit (witness2.inAmt i') (witness2.inPk i') (witness2.inR i') witness2.mint :=
    sameCommitment
  rcases commitment_determines_value_or_collision _ _ _ _ _ _ _ _ hCommitEq with hTupleEq | hH4
  · simp only [Prod.mk.injEq] at hTupleEq
    obtain ⟨hAmt, hPk, hR, hMint⟩ := hTupleEq
    by_cases hSk : witness1.inSk i = witness2.inSk i'
    · exact Or.inl (same_note_same_nullifier witness1 witness2 pubInput1 pubInput2 h1 h2 i i'
        ⟨hAmt, hSk, hR, hMint, sameIndex⟩)
    · have hPkH1 : H1 (witness1.inSk i) = H1 (witness2.inSk i') := hPk
      exact Or.inr (Or.inl ⟨hSk, hPkH1⟩)
  · exact Or.inr (Or.inr hH4)

-- 2e. No same-commitment reuse across txs, unless a hash collision was found.
-- Like 2c, but we assume they use the same commitment + leaf index.
theorem no_commitment_reuse_possible_across_txs_or_collision
  (w1 w2 w2' w3: World)
  (txInputs1 txInputs2: TxInputs)
  (witness1 witness2: Witness)
  (hRel1: RelationS txInputs1.pubInputs witness1)
  (hRel2: RelationS txInputs2.pubInputs witness2)
  (i i': Fin 2)
  (sameIndex: (witness1.openings i).index = (witness2.openings i').index)
  (sameCommitment: witness1.inC i = witness2.inC i')
  (h4: transact txInputs1 w1 w2)
  (h5: ReachableWorld w2 w2') -- Any amount of txs in between after the first txs
  : ¬ transact txInputs2 w2' w3
    ∨ H1Collision (witness1.inSk i) (witness2.inSk i')
    ∨ H4Collision (witness1.inAmt i, witness1.inPk i, witness1.inR i, witness1.mint)
                  (witness2.inAmt i', witness2.inPk i', witness2.inR i', witness2.mint) := by
  -- Case-split proof: the commitment match either really does mean the same nullifier,
  -- which is blocked the same way as in 2c, or it doesn't, which can only be because of a hash collision
  rcases same_commitment_same_nullifier_or_collision witness1 witness2 txInputs1.pubInputs
      txInputs2.pubInputs hRel1 hRel2 i i' sameIndex sameCommitment with hNullEq | hColl
  · exact Or.inl (no_reuse_across_txs_from_nullifier_eq w1 w2 w2' w3 txInputs1 txInputs2 i i' hNullEq h4 h5)
  · exact Or.inr hColl

-- 2f. A single txs can't spend the same commitment at the same leaf index for both
-- inputs, unless a hash collision was found.
theorem no_commitment_reuse_possible_within_txs_or_collision
  (txInputs: TxInputs)
  (witness: Witness)
  (sameIndex: (witness.openings 0).index = (witness.openings 1).index)
  (sameCommitment: witness.inC 0 = witness.inC 1)
  : ¬ RelationS txInputs.pubInputs witness
    ∨ H1Collision (witness.inSk 0) (witness.inSk 1)
    ∨ H4Collision (witness.inAmt 0, witness.inPk 0, witness.inR 0, witness.mint)
                  (witness.inAmt 1, witness.inPk 1, witness.inR 1, witness.mint) := by
  -- Case-split proof: if the witness isn't even valid, we're done.
  -- Otherwise, the commitment match either really does mean the same nullifier, blocked the
  -- same way as in 2d, or it doesn't, which can only be because of a hash collision
  by_cases hRel : RelationS txInputs.pubInputs witness
  · rcases same_commitment_same_nullifier_or_collision witness witness txInputs.pubInputs
        txInputs.pubInputs hRel hRel 0 1 sameIndex sameCommitment with hNullEq | hColl
    · exact absurd hNullEq hRel.noDuplicateNullifiers
    · exact Or.inr hColl
  · exact Or.inl hRel

-- 4. SOL balance correctness. The SOL balance equals deposits minus withdrawals and fees paid
-- Given:
  -- vk for the circuit
  -- an old_world
  -- a new_world
-- When: transact
-- Then: new_world.state.solBalance = old_world.state.solBalance + inputs.extAmt - inputs.f
theorem sol_balance_correctness
  (oldWorld newWorld : World)
  (inputs: TxInputs)
  (h1: transact inputs oldWorld newWorld)
  : (newWorld.state.solBalance : ℤ) = oldWorld.state.solBalance + inputs.extAmt - inputs.f
  := by
  obtain ⟨hpre, heff⟩ := h1
  have hsolvNeg := hpre.poolSolvency.1
  have hsolvNonneg := hpre.poolSolvency.2
  rw [heff.solBalance]
  simp only [transactEffects, transferEffects]
  split_ifs with hz hpos <;> (try dsimp only)
  · -- transfer (extAmt = 0): only the fee leaves the pool, and it never underflows
    have hfle : inputs.f ≤ oldWorld.state.solBalance := by
      rcases Nat.eq_zero_or_pos inputs.f with hf0 | hfpos
      · omega
      · have := hsolvNonneg ⟨by omega, hfpos⟩
        omega
    omega
  · -- deposit (extAmt > 0): the deposit lands first, then the fee is taken out
    have hfle : inputs.f ≤ oldWorld.state.solBalance + inputs.extAmt.natAbs := by
      rcases Nat.eq_zero_or_pos inputs.f with hf0 | hfpos
      · omega
      · have := hsolvNonneg ⟨by omega, hfpos⟩
        omega
    omega
  · -- withdrawal (extAmt < 0): `poolSolvency` guarantees enough balance for both the
    -- withdrawal and the fee, so neither ℕ subtraction underflows
    have hextNeg : inputs.extAmt < 0 := by omega
    have hsolv := hsolvNeg hextNeg
    have habs : |inputs.extAmt| = (inputs.extAmt.natAbs : ℤ) := Int.abs_eq_natAbs inputs.extAmt
    omega

-- 6. A note can only be withdrawn via transact with knowledge of k and r
-- Because we assume a Groth16 proof can only be created with that knowledge.
-- This seems to be exactly the axiom of soundness, but consider the scenario where withdrawing doesn't even check the proof.
-- (Stated ahead of section 5, which relies on 6b for its witness.)
-- 6a. transact fails when the proof is invalid
-- Given:
  -- an old_world
  -- inputs where the proof does not verify
  -- a new_world
-- When: transact
-- Then: fail
-- Immediate in the spec (it is the `validZKP` precondition). Its value is on the code side:
-- the connection theorem shows the program actually checks the proof.
theorem transact_fails_when_proof_invalid
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h1: ¬ Groth16.verify Deployment.vk inputs.π inputs.pubInputs)
  : ¬ transact inputs oldWorld newWorld := by
  intro h2
  exact h1 h2.1.validZKP

-- 6b. A successful transact comes with a witness: private keys, blinding factors,
-- amounts and openings satisfying relation S.
-- Given:
  -- an old_world
  -- a new_world
-- When: transact
-- Then: a witness for the public inputs exists
-- Relies on `Deployment.soundness` (Groth16 knowledge soundness for the deployed key).
theorem transact_implies_witness
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h1: transact inputs oldWorld newWorld)
  : ∃ witness, RelationS inputs.pubInputs witness :=
  Deployment.soundness inputs.π inputs.pubInputs h1.1.validZKP

-- 5. Only deposited coins whose root is in the current history can be withdrawn: transact will fail for a coin that was not added to the tree
-- 5a. transact fails when the root used is not in the history (100 historic roots)
-- Given:
  -- an old_world
  -- inputs whose root is not in the old_world's root history
  -- a new_world
-- When: transact
-- Then: fail
theorem transact_fails_when_root_unknown
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h1: inputs.R ∉ Set.range oldWorld.state.tree.history)
  : ¬ transact inputs oldWorld newWorld := by
  intro h2
  exact h1 h2.1.knownRoot.1

-- 5b. Every non-zero input spent by a successful transact has a valid Merkle opening
-- to a root in the history.
-- Given:
  -- an old_world
  -- a new_world
-- When: transact
-- Then: there is a witness whose non-zero inputs all have valid openings to a known root
-- Note: doesn't show the coin was actually deposited at that position -- see the
-- "GAP: Merkle position binding" note after invariant 7.
theorem transact_implies_valid_openings
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h1: transact inputs oldWorld newWorld)
  : ∃ witness, RelationS inputs.pubInputs witness
    ∧ inputs.R ∈ Set.range oldWorld.state.tree.history
    ∧ ∀ i, witness.inAmt i ≠ 0 → (witness.openings i).Valid (witness.inC i) inputs.R := by
  obtain ⟨witness, hRel⟩ := transact_implies_witness oldWorld newWorld inputs h1
  exact ⟨witness, hRel, h1.1.knownRoot.1, fun i hne => hRel.correctOpenings i hne⟩

-- 7. Root consistency. Transact cannot add a root to history that is not a valid root.
-- Every root added is really a valid root in history OR default value

/-- HELPER `transferEffects` only ever touches `solBalance` and `balances`; the tree is
    untouched either way. -/
lemma transferEffects_tree (inputs: TxInputs) (oldWorld: World) :
    (transferEffects inputs oldWorld).state.tree = oldWorld.state.tree := by
  unfold transferEffects
  split_ifs <;> rfl

-- 7a. Every tree a reachable world can produce is built by a genuine sequence of
-- `appendEffects` calls from `initTree`, not an arbitrary value: `transact` is the only
-- way to change a `Tree`, and it always goes through `appendEffects`.
theorem tree_well_formed
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : ∃ cs: List F, w.state.tree = foldAppend cs initTree := by
  induction h with
  | noStep => exact ⟨[], rfl⟩
  | extend inputs _ transact_proof ih =>
    obtain ⟨cs, hcs⟩ := ih
    obtain ⟨_, hagree⟩ := transact_proof
    refine ⟨cs ++ [inputs.outC0, inputs.outC1], ?_⟩
    rw [hagree.tree]
    simp only [transactEffects, transferEffects_tree, foldAppend, List.foldl_append,
      List.foldl_cons, List.foldl_nil, hcs]

/-- `y` is in the range of `Function.update f i v` only if it's the new value `v` or was
    already in the range of `f`. The generic fact behind "updating the tree's root
    history can only ever add the new root, never invent an unrelated one". -/
lemma mem_range_update_or_mem_range {α β} [DecidableEq α] (f: α → β) (i: α) (v y: β)
    (h: y ∈ Set.range (Function.update f i v)) : y = v ∨ y ∈ Set.range f := by
  obtain ⟨x, hx⟩ := h
  rw [Function.update_apply] at hx
  split_ifs at hx with hxi
  · exact Or.inl hx.symm
  · exact Or.inr ⟨x, hx⟩

-- 7b. Every root that ever lands in `history` is either the untouched default `Z 26` or
-- is genuinely the root of some `appendEffects`-built tree -- never an arbitrary value.

/-- Helper: `appendEffects`'s `history` is always the old `history`, updated at the new root
    slot with the new root -- stated without unfolding how that new root is computed,
    so it composes regardless of the Merkle internals. -/
lemma appendEffects_history (c: F) (t: Tree) :
    (appendEffects c t).history
      = Function.update t.history (t.rootIndex + 1) (appendEffects c t).root := rfl


theorem history_entries_are_genuine_roots
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : ∀ R ∈ Set.range w.state.tree.history,
      R = Z 26 ∨ R = 0 ∨ ∃ cs: List F, R = (foldAppend cs initTree).root := by
  induction h with
  | noStep =>
    intro R hR
    obtain ⟨i, hi⟩ := hR
    simp only [initWorld, initTree] at hi
    split_ifs at hi with hi0
    · exact Or.inl hi.symm
    · exact Or.inr (Or.inl hi.symm)
  | extend inputs h2 transact_proof ih =>
    intro R hR
    obtain ⟨_, hagree⟩ := transact_proof
    rw [hagree.tree] at hR
    -- Expose the two nested `appendEffects` calls (`appendEffects` itself stays
    -- opaque), then peel each one's `history` update off in turn via
    -- `appendEffects_history`, never unfolding the Merkle computation itself.
    simp only [transactEffects, transferEffects_tree] at hR
    rw [appendEffects_history] at hR
    rcases mem_range_update_or_mem_range _ _ _ _ hR with hEq | hR'
    · obtain ⟨cs, hcs⟩ := tree_well_formed cfg balances rentExemptMin _ h2
      refine Or.inr (Or.inr ⟨cs ++ [inputs.outC0, inputs.outC1], ?_⟩)
      have : foldAppend (cs ++ [inputs.outC0, inputs.outC1]) initTree
          = appendEffects inputs.outC1 (appendEffects inputs.outC0 (foldAppend cs initTree)) := by
        simp [foldAppend]
      rw [this, ← hcs]
      exact hEq
    rw [appendEffects_history] at hR'
    rcases mem_range_update_or_mem_range _ _ _ _ hR' with hEq | hR''
    · obtain ⟨cs, hcs⟩ := tree_well_formed cfg balances rentExemptMin _ h2
      refine Or.inr (Or.inr ⟨cs ++ [inputs.outC0], ?_⟩)
      have : foldAppend (cs ++ [inputs.outC0]) initTree
          = appendEffects inputs.outC0 (foldAppend cs initTree) := by
        simp [foldAppend]
      rw [this, ← hcs]
      exact hEq
    · exact ih R hR''

/-
GAP: Merkle position binding. Missing: a valid `Opening` of `c` at index `k` against a
reachable root implies some `appendEffects` call actually wrote `c` there (converse),
and appending more commitments preserves earlier leaves' openings, just extending the
sibling path (forward). Needed by: invariant 2 level 3 (different claimed index isn't
ruled out, converse), invariant 5b (opening valid ⇏ actually deposited, converse), and
invariant 10 (`witness` is a bare hypothesis rather than derived from a real deposit,
forward). Not yet formalized.
-/

-- 8. Note value consistency. A deposited note's value cannot change
-- Note value consistency: if a later input reuses an earlier output's commitment
-- value, it was created with the same (amount, pubkey, blinding, mint), unless an H4
-- collision was found.
theorem note_value_consistency
  (witness1 witness2 : Witness)
  (pubInput1 : PubInputs)
  (j i : Fin 2)
  (h1 : RelationS pubInput1 witness1)
  (hSameCommitment : pubInput1.outCommitments j = witness2.inC i)
  : (witness2.inAmt i, witness2.inPk i, witness2.inR i, witness2.mint)
      = (witness1.outAmt j, witness1.outPk j, witness1.outR j, witness1.mint)
    ∨ H4Collision (witness2.inAmt i, witness2.inPk i, witness2.inR i, witness2.mint)
                  (witness1.outAmt j, witness1.outPk j, witness1.outR j, witness1.mint) := by
  have houtEq := h1.outputCommitmentIntegrity j
  rw [houtEq] at hSameCommitment
  exact commitment_determines_value_or_collision _ _ _ _ _ _ _ _ hSameCommitment.symm

-- 9. Proof binding. The same proof cannot be used for different txInputs.

-- 9a. Groth16 level: the same (vk, π) cannot verify two different public-input
-- vectors, unless an IC relation was found.
theorem proof_binds_to_pubInputs_or_relation
  (π : Groth16.Proof) (x x' : PubInputs)
  (hx : Groth16.verify Deployment.vk π x)
  (hx' : Groth16.verify Deployment.vk π x')
  : x = x' ∨ Groth16.ICRelation Deployment.vk x x' := by
  by_cases heq : x = x'
  · exact Or.inl heq
  · refine Or.inr ⟨heq, ?_⟩
    -- Both equations share `e π.A π.B`; cancel the shared `e vk.α vk.β` and `e π.C vk.δ`
    -- factors (pure group cancellation in `GT`, no bilinearity needed) to land on
    -- `e vkX γ = e vkX' γ`, exactly `ICRelation`'s `eq` field.
    simp only [Groth16.verify] at hx hx'
    exact mul_left_cancel (mul_right_cancel (hx.symm.trans hx'))

-- 9b. Protocol level: the same proof can't be replayed against different TxInputs
-- (different recipient, fee, encrypted outputs, mint, ...) unless an IC relation or a
-- sha256 collision was found.
theorem proof_binds_to_txInputs_or_break
  (inputs1 inputs2 : TxInputs)
  (hSameProof : inputs1.π = inputs2.π)
  (hv1 : proofValid inputs1) (hv2 : proofValid inputs2)
  (hb1 : externalDataBound inputs1) (hb2 : externalDataBound inputs2)
  (hDataDiff : serealizeExternalData inputs1 ≠ serealizeExternalData inputs2)
  : Groth16.ICRelation Deployment.vk inputs1.pubInputs inputs2.pubInputs
    ∨ Sha256Collision (serealizeExternalData inputs1) (serealizeExternalData inputs2) := by
  have hv2' : Groth16.verify Deployment.vk inputs1.π inputs2.pubInputs := hSameProof ▸ hv2
  rcases proof_binds_to_pubInputs_or_relation inputs1.π inputs1.pubInputs inputs2.pubInputs hv1 hv2'
    with hEq | hRel
  · -- Same `pubInputs` forces the same `extDataHash`, which with `externalDataBound` on
    -- both sides forces the same sha256 digest; `hDataDiff` then makes that a collision.
    refine Or.inr ⟨hDataDiff, ?_⟩
    have hED : inputs1.extDataHash = inputs2.extDataHash := by
      simpa [TxInputs.pubInputs] using congrArg PubInputs.extDataHash hEq
    show externalDataHash inputs1 = externalDataHash inputs2
    rw [hb1, hb2, hED]
  · exact Or.inl hRel

-- 10. Any unspent notes can always be spent
--
-- Taken literally this is false: a withdrawal can be genuinely blocked by pool
-- insolvency (`poolSolvent`), a deposit by signer insolvency (`signerSolvent`), a full
-- tree (`treeHasRoom`), or a root that has rotated out of the 100-slot history
-- (`rootKnown`) before a spend lands. Those aren't proof artifacts to route around --
-- they're real protocol constraints -- so the honest completeness statement takes every
-- non-ZKP precondition as a hypothesis and shows the *only* remaining obstacle, the ZK
-- proof itself, is never one: given a witness, `Deployment.completeness` always produces
-- a proof that makes `transact` go through.
--
-- GAP: `witness` is a bare hypothesis, not derived from an actual prior deposit -- see
-- the "GAP: Merkle position binding" note after invariant 7.
theorem unspent_note_is_spendable
  (oldWorld: World) (inputs: TxInputs) (witness: Witness)
  (hRel: RelationS inputs.pubInputs witness)
  (hRoot: rootKnown oldWorld.state.tree inputs.R)
  (hData: externalDataBound inputs)
  (hFee: feeSufficient oldWorld.state.config inputs.extAmt inputs.f)
  (hPubAmt: pubAmtConsistent inputs.extAmt inputs.f inputs.pubAmt)
  (hFresh: nullifiersFresh oldWorld.state.nullifiers inputs.k0 inputs.k1)
  (hDistinct: nullifiersDistinct inputs.k0 inputs.k1)
  (hDeposit: depositWithinLimit oldWorld.state.config inputs.extAmt)
  (hSolvent: poolSolvent oldWorld.state.solBalance oldWorld.rentExemptMin inputs.extAmt inputs.f)
  (hSignerSolvent: signerSolvent oldWorld.balances inputs.s inputs.extAmt)
  (hRoom: treeHasRoom oldWorld.state.tree)
  : ∃ π, transact { inputs with π := π } oldWorld (transactEffects { inputs with π := π } oldWorld) := by
  obtain ⟨π, hπ⟩ := Deployment.completeness inputs.pubInputs witness hRel
  refine ⟨π, ⟨?_, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => rfl⟩⟩
  exact {
    knownRoot := hRoot
    externalDataBinding := hData
    minimumFee := hFee
    pubAmtConsistency := hPubAmt
    validZKP := hπ
    newNullifiers := hFresh
    distinctNullifiers := hDistinct
    signerSolvency := hSignerSolvent
    depositLimit := hDeposit
    poolSolvency := hSolvent
    treeNotFull := hRoom
  }
