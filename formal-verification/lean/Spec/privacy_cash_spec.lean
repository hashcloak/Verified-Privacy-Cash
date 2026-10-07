import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

--///////// Note: SOL ONLY. In Phase 2 we'll distinguish between SOL and SPL.

-- TODO review what has been translated so far. There are definitely errors in the translation still.

-- Everything below lives in `LeanSpec`, not the root namespace: several names here
-- (`Tree`, `Byte`, ...) are generic enough to collide with Mathlib/Aeneas root-level
-- declarations once a file imports both this spec and `code_model` (exactly what a
-- connection theorem needs to do). Callers that need both use `open LeanSpec (name1
-- name2 ...)` to selectively pull in what they need without pulling in the colliding
-- names -- see Connection/Basic.lean.
namespace LeanSpec

--/////////////////////////////////////////
-- Definitions
--/////////////////////////////////////////
def p: ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- Needed by invariant 13's field-to-`ℤ` lifting lemmas (`ZMod.natCast_rightInverse` /
    `ZMod.val_cast_of_lt` etc. all require `[NeZero p]`); `p` is a specific nonzero
    numeral, but being a `def` (not a literal in typeclass search's eyes), the instance
    needs stating explicitly. -/
instance : NeZero p := ⟨by decide⟩

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

/-- Two different argument pairs with the same `H2` output -- the binary Merkle hash used
    in `Opening.calcRoot` and `appendEffects`. Needed by invariant 7 (Merkle position
    binding), the first place this file reasons about `H2` collision resistance. -/
structure H2Collision (a b : F × F) : Prop where
  ne : a ≠ b
  eq : H2 a.1 a.2 = H2 b.1 b.2

/-- Two different byte strings whose little-endian, mod-`p` reduced `sha256` digests
    collide -- the actual hash used to bind external transaction data
    (`externalDataHash`) into the circuit's public inputs. A weaker (hence easier to
    obtain) break than a raw `sha256` collision, since it also holds when two distinct
    digests happen to agree mod `p`. -/
structure Sha256Collision (a b : Bytes) : Prop where
  ne : a ≠ b
  eq : (natOfLE (sha256 a) : F) = (natOfLE (sha256 b) : F)

/-- An `H4` preimage of the literal field element `0` -- a different flavor of break than
    the Collision structures above (which compare two *different* inputs with the same
    output). `Z 0`, the Merkle tree's zero-padding leaf value, is literally `0`
    (`Z`'s definition below); an unwritten leaf position's *only* validly-openable value
    is `0` (invariant 7a). So claiming a nonzero note at a position that was never really
    written requires producing `(amt, pk, r, mint)` with `commit amt pk r mint = 0` --
    not a collision against another real commitment, but a preimage of this one, public,
    fixed constant. Needed by invariant 13's value bound, the first place this file has
    to reason about an unwritten leaf's commitment rather than just compare two written
    ones. -/
structure H4ZeroPreimage (a : F × F × F × F) : Prop where
  eq : H4 a.1 a.2.1 a.2.2.1 a.2.2.2 = 0

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

  The $extAmt=0$ case is defined here for `transferEffects` alone, but is unreachable
  through `transact`: `pubAmtConsistent` (`transactPreconditions.pubAmtConsistency`)
  rejects $extAmt=0$ outright, matching `check_public_amount`'s guard.
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
          -- `poolSolvency` rules out (see `sol_balance_correctness_step`), and `ℕ` doesn't
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
-- The middle conjunct is `extAmt ≥ 0`, not `extAmt > 0`: the program's guard
-- (`ext_amount >= 0 && ext_amount_fr <= fee_fr`, utils.rs) treats `extAmt = 0` as a
-- deposit that must also clear the fee, which it never can since `f : ℕ` can't be
-- negative. So `extAmt = 0` is always rejected -- a zero-amount "transfer" is
-- unreachable through `transact` (see the note above `transferEffects`).
def pubAmtConsistent (extAmt: ℤ) (f: ℕ) (pubAmt: F): Prop :=
  -- reference i64::MIN https://doc.rust-lang.org/std/i64/constant.MIN.html
  extAmt ≠ -9_223_372_036_854_775_808 ∧
  (extAmt ≥ 0 → extAmt > f) ∧
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

-- The pool account is created holding exactly its rent-exempt minimum (Anchor `init` funds
-- it), and `solBalance` counts the pool's total lamports, rent reserve included -- the same
-- reading `poolSolvent` uses (`solBalance ≥ … + rentExemptMin`).
def initWorld(config: config)(balances: Pubkey → ℕ)(rentExemptMin: ℕ) : World := {
  state := {
    tree := initTree
    nullifiers := ∅
    solBalance := rentExemptMin
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

-- `ReachableWorld`, plus the list of `TxInputs` actually applied, in order. A ghost
-- trace: the system doesn't store it; it only lets invariants talk about the real history.
inductive ReachableTrace: World → List TxInputs → World → Prop where
 | noStep(w1: World): ReachableTrace w1 [] w1
 | extend{w1 w2 w3: World}{txs: List TxInputs}(txInputs: TxInputs):
      ReachableTrace w1 txs w2 →
      transact txInputs w2 w3 →
      ReachableTrace w1 (txs ++ [txInputs]) w3

lemma ReachableTrace.toReachableWorld {w1 w2: World} {txs: List TxInputs}
    (h: ReachableTrace w1 txs w2) : ReachableWorld w1 w2 := by
  induction h with
  | noStep => exact ReachableWorld.noStep _
  | extend inputs _ transact_proof ih => exact ReachableWorld.extend inputs ih transact_proof

lemma ReachableWorld.exists_trace {w1 w2: World}
    (h: ReachableWorld w1 w2) : ∃ txs, ReachableTrace w1 txs w2 := by
  induction h with
  | noStep => exact ⟨[], ReachableTrace.noStep _⟩
  | extend inputs _ transact_proof ih =>
    obtain ⟨txs, htxs⟩ := ih
    exact ⟨txs ++ [inputs], ReachableTrace.extend inputs htxs transact_proof⟩

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
-- Level 3: commitment level (this uses hash collision resistance). A spend claiming a
-- *different* leaf index for a commitment it already spent is closed by
-- `witness_opening_is_genuine_or_collision` (invariant 7c): any claimed index either
-- genuinely holds that commitment (a real, separately-nullified deposit, not a reuse) or
-- an H2 collision was found. It has to live after invariant 7 rather than here.

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

-- 3. SOL balance correctness. The pool's SOL balance always equals the net of every
-- deposit, withdrawal and fee ever processed through `transact`.

-- Proof for a single step executing transact: `extAmt` lands in the pool for a deposit
-- and leaves it for a withdrawal (mirrored the other way on `balances` by
-- `transferEffects`), and the fee `f` always leaves the pool to the fee recipient.
-- Given:
  -- an old_world
  -- a new_world
-- When: transact
-- Then: new_world.state.solBalance = old_world.state.solBalance + inputs.extAmt - inputs.f
lemma sol_balance_correctness_step
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

-- For the transactions `txs` actually applied since `initWorld` (whose `solBalance` starts
-- at the rent reserve), `solBalance` = rent reserve + Σ (extAmt − f) over `txs`.
-- Given:
  -- a world w reached from initWorld via the trace txs
-- Then: solBalance = txs.foldl (· + extAmt − f) rentExemptMin
theorem sol_balance_correctness_trace
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World) (txs: List TxInputs)
  (h: ReachableTrace (initWorld cfg balances rentExemptMin) txs w)
  : (w.state.solBalance : ℤ)
      = txs.foldl (fun acc (tx: TxInputs) => acc + tx.extAmt - tx.f) (rentExemptMin : ℤ) := by
  induction h with
  | noStep => simp [initWorld]
  | extend inputs _ transact_proof ih =>
    have hstep := sol_balance_correctness_step _ _ inputs transact_proof
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep, ih]

/-- HELPER: trace-free form of 3, used by `Connection/Reachable.lean`. Weaker: `∃ txs`
    alone could be any list with the right sum. -/
theorem sol_balance_correctness
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : ∃ txs: List TxInputs,
      (w.state.solBalance : ℤ)
        = txs.foldl (fun acc (tx: TxInputs) => acc + tx.extAmt - tx.f) (rentExemptMin : ℤ) := by
  obtain ⟨txs, htxs⟩ := h.exists_trace
  exact ⟨txs, sol_balance_correctness_trace cfg balances rentExemptMin w txs htxs⟩

-- 4. Spending a note via `transact` requires knowing its opening; the private key,
-- blinding factor and amount behind its commitment (`written_spec.md`'s informal
-- "knowledge of k, r"; here, a full `Witness` satisfying `RelationS`). Follows from
-- Groth16 soundness (`Deployment.soundness`), but only because `transact` checks the proof
-- (imagine transact wouldn't even check the proof, then soundness doesn't save us)

-- The only way to spend a note is to get `transact` to accept, and the only way to get it
-- to accept is to hand it a proof that actually verifies. And if you can do that, you had the witness values.
-- Given:
  -- an old_world
  -- a new_world
-- Then:
  -- (a) if the proof doesn't verify, transact fails.
  -- (b) if transact succeeds, a witness exists satisfying `RelationS` for the public inputs
theorem transact_requires_valid_proof_and_witness
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  : (¬ Groth16.verify Deployment.vk inputs.π inputs.pubInputs → ¬ transact inputs oldWorld newWorld)
    ∧ (transact inputs oldWorld newWorld → ∃ witness, RelationS inputs.pubInputs witness) := by
  refine ⟨fun h1 h2 => h1 h2.1.validZKP, fun h1 => ?_⟩
  exact Deployment.soundness inputs.π inputs.pubInputs h1.1.validZKP

/-- HELPER: `transferEffects` doesn't touch the tree. -/
lemma transferEffects_tree (inputs: TxInputs) (oldWorld: World) :
    (transferEffects inputs oldWorld).state.tree = oldWorld.state.tree := by
  unfold transferEffects
  split_ifs <;> rfl

/-- HELPER: every reachable tree is `foldAppend cs initTree` for some `cs`. -/
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

/-- HELPER: a reachable tree stays under its `2^26`-leaf capacity (`treeNotFull` leaves
    room for the two appended outputs). -/
lemma reachable_tree_lt
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : w.state.tree.nextIndex < 2^26 := by
  induction h with
  | noStep => simp [initWorld, initTree]
  | extend inputs _ transact_proof _ =>
    obtain ⟨hpre, hagree⟩ := transact_proof
    have hroom := hpre.treeNotFull
    unfold treeHasRoom at hroom
    rw [hagree.tree]
    simp only [transactEffects, transferEffects_tree]
    have hstep : ∀ t : Tree, (appendEffects inputs.outC1 (appendEffects inputs.outC0 t)).nextIndex
        = t.nextIndex + 2 := fun t => rfl
    rw [hstep]
    omega

/-- HELPER: a value in the range of `Function.update f i v` is `v`, or was already in
    the range of `f`. -/
lemma mem_range_update_or_mem_range {α β} [DecidableEq α] (f: α → β) (i: α) (v y: β)
    (h: y ∈ Set.range (Function.update f i v)) : y = v ∨ y ∈ Set.range f := by
  obtain ⟨x, hx⟩ := h
  rw [Function.update_apply] at hx
  split_ifs at hx with hxi
  · exact Or.inl hx.symm
  · exact Or.inr ⟨x, hx⟩

/-- HELPER: `appendEffects` writes its new root into the next `history` slot. -/
lemma appendEffects_history (c: F) (t: Tree) :
    (appendEffects c t).history
      = Function.update t.history (t.rootIndex + 1) (appendEffects c t).root := rfl

/-- HELPER: `nextIndex` of `foldAppend cs initTree` is `cs.length`. -/
lemma foldAppend_nextIndex (cs : List F) : (foldAppend cs initTree).nextIndex = cs.length := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    have : foldAppend (ys ++ [y]) initTree = appendEffects y (foldAppend ys initTree) := by
      simp [foldAppend]
    rw [this]
    show (foldAppend ys initTree).nextIndex + 1 = (ys ++ [y]).length
    rw [ih]; simp

-- 5. Root consistency: transact never writes an invalid root into `history`.
-- For the list `cs` of commitments actually appended (in order), every `history` entry
-- is `0` (an untouched slot, see `initTree`) or the root after the first `k` appends
-- (`k = 0` is the empty-tree root `Z 26`). The same `cs` builds the current tree, so
-- each root is a state the tree really passed through.
theorem history_entries_are_prefix_roots
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : ∃ cs: List F, w.state.tree = foldAppend cs initTree ∧
      ∀ R ∈ Set.range w.state.tree.history,
        R = 0 ∨ ∃ k ≤ cs.length, R = (foldAppend (cs.take k) initTree).root := by
  induction h with
  | noStep =>
    refine ⟨[], rfl, ?_⟩
    intro R hR
    obtain ⟨i, hi⟩ := hR
    simp only [initWorld, initTree] at hi
    split_ifs at hi
    · exact Or.inr ⟨0, le_rfl, hi.symm⟩
    · exact Or.inl hi.symm
  | extend inputs _ transact_proof ih =>
    obtain ⟨cs, hcs, hhist⟩ := ih
    obtain ⟨_, hagree⟩ := transact_proof
    -- Appending more commitments continues from the tree `cs` already built.
    have hfold : ∀ ys : List F,
        foldAppend (cs ++ ys) initTree = foldAppend ys (foldAppend cs initTree) := by
      intro ys; simp [foldAppend, List.foldl_append]
    refine ⟨cs ++ [inputs.outC0, inputs.outC1], ?_, ?_⟩
    · rw [hagree.tree, hfold, ← hcs]
      simp only [transactEffects, transferEffects_tree, foldAppend, List.foldl_cons,
        List.foldl_nil]
    · intro R hR
      rw [hagree.tree] at hR
      -- Peel the two `history` updates off in turn (newest first), never unfolding the
      -- Merkle computation inside `appendEffects`.
      simp only [transactEffects, transferEffects_tree] at hR
      rw [appendEffects_history] at hR
      rcases mem_range_update_or_mem_range _ _ _ _ hR with hEq | hR'
      · -- root after appending both outputs: the full new list, `k = cs.length + 2`
        refine Or.inr ⟨cs.length + 2, by simp, ?_⟩
        rw [List.take_of_length_le (by simp), hfold, ← hcs]
        exact hEq
      rw [appendEffects_history] at hR'
      rcases mem_range_update_or_mem_range _ _ _ _ hR' with hEq | hR''
      · -- intermediate root after appending `outC0` only: `k = cs.length + 1`
        refine Or.inr ⟨cs.length + 1, by simp, ?_⟩
        rw [show (cs ++ [inputs.outC0, inputs.outC1]).take (cs.length + 1)
            = cs ++ [inputs.outC0] by rw [List.take_append]; simp, hfold, ← hcs]
        exact hEq
      · -- an older entry: its prefix of `cs` is also a prefix of the extended list
        rcases hhist R hR'' with h0 | ⟨k, hk, hRk⟩
        · exact Or.inl h0
        · refine Or.inr ⟨k, by simp; omega, ?_⟩
          rw [List.take_append_of_le_length hk]
          exact hRk

/-- HELPER: weaker form of invariant 5 (the root of *some* `cs`), the shape 7d uses.
    Not a security statement on its own. -/
lemma history_entries_are_genuine_roots
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : ∀ R ∈ Set.range w.state.tree.history,
      R = Z 26 ∨ R = 0 ∨ ∃ cs: List F, cs.length < 2^26 ∧ R = (foldAppend cs initTree).root := by
  obtain ⟨cs, hcs, hhist⟩ := history_entries_are_prefix_roots cfg balances rentExemptMin w h
  have hlt : cs.length < 2^26 := by
    have := reachable_tree_lt cfg balances rentExemptMin w h
    rwa [hcs, foldAppend_nextIndex] at this
  intro R hR
  rcases hhist R hR with h0 | ⟨k, hk, hRk⟩
  · exact Or.inr (Or.inl h0)
  · exact Or.inr (Or.inr ⟨cs.take k, by simp; omega, hRk⟩)

-- 6. Root binding: `transact` only accepts a spend against a root in `history`.
-- 6a: an unknown root makes transact fail. 6b: on success, every non-zero input has a
-- valid Merkle opening against that root. With invariant 5 (history roots are real
-- tree states), no spend uses a forged root. That the note sits at the claimed leaf
-- is shown later, in 7d (`transact_implies_deposited_openings`).
-- 6a. transact fails when the root used is not in the history (100 historic roots)
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

-- 6b. On success, every non-zero input has a valid Merkle opening to a known root.
-- Given:
  -- an old_world
  -- a new_world
-- When: transact
-- Then: there is a witness whose non-zero inputs all have valid openings to a known root
theorem transact_implies_valid_openings
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h1: transact inputs oldWorld newWorld)
  : ∃ witness, RelationS inputs.pubInputs witness
    ∧ inputs.R ∈ Set.range oldWorld.state.tree.history
    ∧ ∀ i, witness.inAmt i ≠ 0 → (witness.openings i).Valid (witness.inC i) inputs.R := by
  obtain ⟨witness, hRel⟩ := (transact_requires_valid_proof_and_witness oldWorld newWorld inputs).2 h1
  exact ⟨witness, hRel, h1.1.knownRoot.1, fun i hne => hRel.correctOpenings i hne⟩

-- 7. Merkle position binding. `Opening.Valid` only says the path hashes to the root,
-- not that `leaf` is what the tree holds at `index`. 7a: a valid opening's leaf is the
-- real leaf at its index, or an `H2` collision. 7b: a deposited leaf keeps a valid
-- opening as more leaves are appended. Used by invariants 2 (via 7c), 6 (via 7d) and 10.

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

lemma foldUpTo_congr {α : Type} : ∀ (n : ℕ) {f f' : α → ℕ → α} (x : α),
    (∀ y k, k < n → f y k = f' y k) → foldUpTo f n x = foldUpTo f' n x
  | 0, _, _, x, _ => by simp [foldUpTo]
  | (n+1), f, f', x, hh => by
    show f (foldUpTo f n x) n = f' (foldUpTo f' n x) n
    rw [foldUpTo_congr n x (fun y k hk => hh y k (Nat.lt_succ_of_lt hk))]
    exact hh _ n (Nat.lt_succ_self n)

lemma fin_foldl_eq_foldUpTo {α : Type} :
    ∀ (n : ℕ) (g : α → Fin n → α) (x : α),
      Fin.foldl n g x = foldUpTo (fun x h => if hh : h < n then g x ⟨h, hh⟩ else x) n x
  | 0, g, x => by simp [foldUpTo]
  | (n+1), g, x => by
    rw [Fin.foldl_succ_last]
    have ih := fin_foldl_eq_foldUpTo n (fun x (i : Fin n) => g x i.castSucc) x
    rw [ih]
    have hagree : ∀ (y : α) (k : ℕ), k < n →
        (fun x h => if hh : h < n then g x (⟨h, hh⟩ : Fin n).castSucc else x) y k
        = (fun x h => if hh : h < n+1 then g x ⟨h, hh⟩ else x) y k := by
      intro y k hk
      simp only [dif_pos hk, dif_pos (Nat.lt_succ_of_lt hk), Fin.castSucc_mk]
    rw [foldUpTo_congr n x hagree]
    show g (foldUpTo (fun x h => if hh : h < n+1 then g x ⟨h,hh⟩ else x) n x) (Fin.last n)
       = foldUpTo (fun x h => if hh : h < n+1 then g x ⟨h,hh⟩ else x) (n+1) x
    simp only [foldUpTo, dif_pos (Nat.lt_succ_self n)]
    rfl

/-- `fin_foldl_eq_foldUpTo` for an `f` that agrees with `g` pointwise. -/
lemma fin_foldl_eq_foldUpTo_plain {α : Type} {n : ℕ} (g : α → Fin n → α) (f : α → ℕ → α)
    (hagree : ∀ x (h : ℕ) (hh : h < n), f x h = g x ⟨h, hh⟩) (x : α) :
    Fin.foldl n g x = foldUpTo f n x := by
  rw [fin_foldl_eq_foldUpTo n g x]
  apply foldUpTo_congr
  intro y k hk
  rw [dif_pos hk, hagree y k hk]

-- HELPER: small `Nat.testBit`/`>>>` facts the carry-propagation arguments below rely on.

lemma testBit_shiftRight_eq (k h : ℕ) : Nat.testBit k h = decide ((k >>> h) % 2 = 1) := by
  rw [← Nat.testBit_zero (k >>> h), Nat.testBit_shiftRight, Nat.add_zero]

lemma shiftRight_succ_eq (k h : ℕ) : k >>> h = 2 * (k >>> (h+1)) + (k >>> h) % 2 := by
  rw [Nat.shiftRight_succ]; omega

lemma div_two_shiftRight (n h : ℕ) : n >>> (h+1) = (n / 2) >>> h := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, pow_succ, Nat.div_div_eq_div_mul,
      Nat.mul_comm]

/-- Binary increment: if bit `h` of `n+1` is set, either it was already set (and the
    height-`h` block index is unchanged), or it was just flipped (and the index moves up
    by one). -/
lemma testBit_succ_cases : ∀ (h n : ℕ), Nat.testBit (n+1) h = true →
    (Nat.testBit n h = true ∧ (n+1) >>> h = n >>> h)
    ∨ (Nat.testBit n h = false ∧ (n+1) >>> h = n >>> h + 1)
  | 0, n, hb => by
    right
    have h0 : Nat.testBit n 0 = decide (n % 2 = 1) := Nat.testBit_zero n
    have h1 : Nat.testBit (n+1) 0 = decide ((n+1) % 2 = 1) := Nat.testBit_zero (n+1)
    rw [h1] at hb
    refine ⟨?_, by simp⟩
    rw [h0]
    simp only [decide_eq_true_eq] at hb
    simp only [decide_eq_false_iff_not]
    omega
  | (h+1), n, hb => by
    rw [Nat.testBit_succ] at hb
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- `n` even: incrementing only ever touches bit 0, so bit `h+1` (and everything at
      -- or above it) is untouched -- `(n+1)/2 = n/2`, so the recursion doesn't even fire.
      have hnd : n / 2 = m := by omega
      have hn1d : (n+1) / 2 = m := by omega
      rw [hn1d] at hb
      rw [Nat.testBit_succ, hnd]
      exact Or.inl ⟨hb, by rw [div_two_shiftRight, div_two_shiftRight, hnd, hn1d]⟩
    · -- `n` odd: bit 0 carries, so whether bit `h+1` (and above) changes reduces to the
      -- same question one level down, for `n/2`.
      have hnd : n / 2 = m := by omega
      have hn1d : (n+1) / 2 = m + 1 := by omega
      rw [hn1d] at hb
      rw [Nat.testBit_succ, hnd]
      rcases testBit_succ_cases h m hb with ⟨hbt, hs⟩ | ⟨hbf, hs⟩
      · exact Or.inl ⟨hbt, by rw [div_two_shiftRight, div_two_shiftRight, hnd, hn1d]; exact hs⟩
      · exact Or.inr ⟨hbf, by rw [div_two_shiftRight, div_two_shiftRight, hnd, hn1d]; exact hs⟩

lemma div_mul_le (n h : ℕ) : (n >>> h) * 2^h ≤ n := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_mul_le_self n (2^h)

/-- The block after leaf `n`'s height-`h` block starts after position `n`. -/
lemma succ_le_shiftRight_succ_mul (n h : ℕ) : n + 1 ≤ (n >>> h + 1) * 2^h := by
  rw [Nat.shiftRight_eq_div_pow]
  have hpos : 0 < 2^h := Nat.two_pow_pos h
  have hmod : n % 2^h < 2^h := Nat.mod_lt _ hpos
  have hdm : n / 2^h * 2^h + n % 2^h = n := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod n (2^h)
  have hkey : (n/2^h + 1) * 2^h = n/2^h*2^h + 2^h := by ring
  rw [hkey]
  omega

-- HELPER: `treeHash` under appending: a block inside the old list doesn't change
-- (`treeHash_ext`), and a block past the end is the zero hash (`treeHash_zero`).

lemma leafAt_append_left (cs extra : List F) (i : ℕ) (h : i < cs.length) :
    leafAt (cs ++ extra) i = leafAt cs i := by
  unfold leafAt
  have hlen : (cs ++ extra).length = cs.length + extra.length := by simp
  rw [dif_pos (by omega : i < (cs ++ extra).length), dif_pos h, List.getElem_append_left h]

lemma leafAt_own (cs : List F) (y : F) : leafAt (cs ++ [y]) cs.length = y := by
  unfold leafAt
  rw [dif_pos (by simp : cs.length < (cs ++ [y]).length)]
  simp

lemma treeHash_ext (cs extra : List F) : ∀ (h idx : ℕ), (idx+1) * 2^h ≤ cs.length →
    treeHash (cs ++ extra) h idx = treeHash cs h idx
  | 0, idx, hb => by
    simp only [treeHash]
    apply leafAt_append_left
    omega
  | h+1, idx, hb => by
    simp only [treeHash]
    have hkey : (idx+1)*2^(h+1) = (2*idx+2)*2^h := by ring
    rw [hkey] at hb
    have hleft : (2*idx+1) * 2^h ≤ cs.length :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) hb
    have hright : (2*idx+1+1) * 2^h ≤ cs.length := by
      rw [show 2*idx+1+1 = 2*idx+2 from rfl]; exact hb
    rw [treeHash_ext cs extra h (2*idx) hleft, treeHash_ext cs extra h (2*idx+1) hright]

lemma treeHash_zero (cs : List F) : ∀ (h idx : ℕ), cs.length ≤ idx * 2^h →
    treeHash cs h idx = Z h
  | 0, idx, hb => by
    simp only [treeHash, leafAt]
    rw [dif_neg (by omega)]
  | h+1, idx, hb => by
    simp only [treeHash, Z]
    have hkey : idx * 2^(h+1) = (2*idx) * 2^h := by ring
    rw [hkey] at hb
    have h1 : cs.length ≤ (2*idx) * 2^h := hb
    have h2 : cs.length ≤ (2*idx+1) * 2^h := by
      have hkey2 : (2*idx+1)*2^h = (2*idx)*2^h + 2^h := by ring
      rw [hkey2]
      exact le_trans h1 (Nat.le_add_right _ _)
    rw [treeHash_zero cs h (2*idx) h1, treeHash_zero cs h (2*idx+1) h2]

-- HELPER: the canonical opening of any `k` hashes to the tree's root (pure path
-- arithmetic, independent of `appendEffects`).

lemma calcRoot_canonicalOpening_aux (cs : List F) (k : ℕ) :
    ∀ H : ℕ, foldUpTo (fun acc h =>
        if Nat.testBit k h then H2 (treeHash cs h (siblingIdx k h)) acc
        else H2 acc (treeHash cs h (siblingIdx k h))) H (leafAt cs k)
      = treeHash cs H (k >>> H) := by
  intro H
  induction H with
  | zero => simp [foldUpTo, treeHash]
  | succ H ih =>
    show (fun acc h =>
        if Nat.testBit k h then H2 (treeHash cs h (siblingIdx k h)) acc
        else H2 acc (treeHash cs h (siblingIdx k h)))
      (foldUpTo (fun acc h =>
        if Nat.testBit k h then H2 (treeHash cs h (siblingIdx k h)) acc
        else H2 acc (treeHash cs h (siblingIdx k h))) H (leafAt cs k)) H
      = treeHash cs (H+1) (k >>> (H+1))
    rw [ih]
    have htb := testBit_shiftRight_eq k H
    have hshift := shiftRight_succ_eq k H
    show (if Nat.testBit k H then H2 (treeHash cs H (siblingIdx k H)) (treeHash cs H (k >>> H))
          else H2 (treeHash cs H (k >>> H)) (treeHash cs H (siblingIdx k H)))
       = H2 (treeHash cs H (2*(k >>> (H+1)))) (treeHash cs H (2*(k >>> (H+1))+1))
    by_cases hb : Nat.testBit k H = true
    · have h2 : (k >>> H) % 2 = 1 := of_decide_eq_true (htb.symm.trans hb)
      have hidx : siblingIdx k H = 2 * (k >>> (H+1)) := by
        unfold siblingIdx; rw [if_pos hb]; omega
      have hown : k >>> H = 2 * (k >>> (H+1)) + 1 := by omega
      simp only [hb, if_true, hidx, hown]
    · have hbf : Nat.testBit k H = false := by simpa using hb
      have h2 : (k >>> H) % 2 ≠ 1 := of_decide_eq_false (htb.symm.trans hbf)
      have hidx : siblingIdx k H = 2 * (k >>> (H+1)) + 1 := by
        unfold siblingIdx; rw [if_neg hb]; omega
      have hown : k >>> H = 2 * (k >>> (H+1)) := by omega
      simp [hbf, hidx, hown]

lemma calcRoot_canonicalOpening (cs : List F) (k : Fin (2^26)) :
    (canonicalOpening cs k).calcRoot (leafAt cs k.val) = treeHash cs 26 0 := by
  unfold Opening.calcRoot
  rw [fin_foldl_eq_foldUpTo_plain _
    (fun acc h => if Nat.testBit k.val h then H2 (treeHash cs h (siblingIdx k.val h)) acc
        else H2 acc (treeHash cs h (siblingIdx k.val h)))
    (by intro x h hh; simp [canonicalOpening, Opening.accIsRight])]
  have haux := calcRoot_canonicalOpening_aux cs k.val 26
  have hk0 : (k:ℕ) >>> 26 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt k.isLt
  rw [hk0] at haux
  exact haux

-- HELPER: `appendEffects` is correct: appending `y` gives the `treeHash` root, and
-- updates exactly the right `subtrees` slots, each to its completed block (the standard
-- incremental Merkle tree invariant, proved rather than assumed).

/-- `appendEffects`'s per-height loop body, with `nextIndex` abstracted to `n`. -/
def appendBody (n : ℕ) : (F × (Fin 26 → F)) → Fin 26 → (F × (Fin 26 → F)) :=
  fun (current, subtrees) height =>
    if Nat.testBit n height.val then (H2 (subtrees height) current, subtrees)
    else (H2 current (Z height.val), Function.update subtrees height current)

def appendBodyN (n : ℕ) : (F × (Fin 26 → F)) → ℕ → (F × (Fin 26 → F)) :=
  fun x h => if hh : h < 26 then appendBody n x ⟨h, hh⟩ else x

lemma appendEffects_eq (c : F) (t : Tree) :
    (appendEffects c t).root = (Fin.foldl 26 (appendBody t.nextIndex) (c, t.subtrees)).1
    ∧ (appendEffects c t).subtrees = (Fin.foldl 26 (appendBody t.nextIndex) (c, t.subtrees)).2 := by
  constructor <;> rfl

/-- Loop invariant of `appendEffects` after the first `H ≤ 26` heights: the running hash
    is the block containing position `n`; each processed slot (`h < H`) is unchanged if
    bit `h` of `n` is set, else holds the just-completed block; other slots are
    untouched. Used at `H = 26` below. -/
lemma appendFold_aux (n : ℕ) (cs : List F) (hcs : cs.length = n) (y : F)
    (subOld : Fin 26 → F)
    (hSubInv : ∀ h : Fin 26, Nat.testBit n h.val = true →
        subOld h = treeHash cs h.val (siblingIdx n h.val)) :
    ∀ H : ℕ, H ≤ 26 →
      (foldUpTo (appendBodyN n) H (y, subOld)).1 = treeHash (cs ++ [y]) H (n >>> H)
      ∧ (∀ h : Fin 26, h.val < H →
          (foldUpTo (appendBodyN n) H (y, subOld)).2 h
          = if Nat.testBit n h.val then subOld h else treeHash (cs++[y]) h.val (n >>> h.val))
      ∧ (∀ h : Fin 26, ¬ h.val < H → (foldUpTo (appendBodyN n) H (y, subOld)).2 h = subOld h) := by
  intro H
  induction H with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · show y = treeHash (cs ++ [y]) 0 (n >>> 0)
      rw [Nat.shiftRight_zero]
      show y = leafAt (cs ++ [y]) n
      rw [← hcs]
      exact (leafAt_own cs y).symm
    · intro h hh; omega
    · intro h _; rfl
  | succ H ih =>
    intro hHb
    obtain ⟨ihc, ih1, ih2⟩ := ih (by omega)
    have hHlt : H < 26 := by omega
    set cur := (foldUpTo (appendBodyN n) H (y, subOld)).1 with hcur_def
    set sub := (foldUpTo (appendBodyN n) H (y, subOld)).2 with hsub_def
    have hpair : foldUpTo (appendBodyN n) H (y, subOld) = (cur, sub) := by
      rw [hcur_def, hsub_def]
    have hstep : foldUpTo (appendBodyN n) (H+1) (y, subOld) = appendBody n (cur, sub) ⟨H, hHlt⟩ := by
      show appendBodyN n (foldUpTo (appendBodyN n) H (y, subOld)) H = _
      rw [hpair]
      unfold appendBodyN
      rw [dif_pos hHlt]
    have hboundOld : (n >>> H) * 2^H ≤ n := div_mul_le n H
    by_cases hb : Nat.testBit n H = true
    · -- absorb branch: the just-completed block at height `H` (`n`'s ancestor there)
      -- combines with the already-stored left sibling; `subtrees` doesn't change.
      have hsubH : sub ⟨H, hHlt⟩ = subOld ⟨H, hHlt⟩ := ih2 ⟨H, hHlt⟩ (by simp)
      have hfst : (appendBody n (cur, sub) ⟨H, hHlt⟩).1 = H2 (sub ⟨H,hHlt⟩) cur := by
        show (if Nat.testBit n H then (H2 (sub ⟨H,hHlt⟩) cur, sub)
              else (H2 cur (Z H), Function.update sub ⟨H,hHlt⟩ cur)).1 = H2 (sub ⟨H,hHlt⟩) cur
        rw [if_pos hb]
      have hsnd : (appendBody n (cur, sub) ⟨H, hHlt⟩).2 = sub := by
        show (if Nat.testBit n H then (H2 (sub ⟨H,hHlt⟩) cur, sub)
              else (H2 cur (Z H), Function.update sub ⟨H,hHlt⟩ cur)).2 = sub
        rw [if_pos hb]
      have hkey : n >>> H = 2 * (n >>> (H+1)) + 1 := by
        have hs := shiftRight_succ_eq n H
        have h2 : (n >>> H) % 2 = 1 :=
          of_decide_eq_true ((testBit_shiftRight_eq n H).symm.trans hb)
        omega
      have hkeySib : siblingIdx n H = 2 * (n >>> (H+1)) := by
        unfold siblingIdx; rw [if_pos hb]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep, hfst]
        rw [hsubH, hSubInv ⟨H,hHlt⟩ hb]
        show H2 (treeHash cs H (siblingIdx n H)) cur
           = H2 (treeHash (cs++[y]) H (2*(n >>> (H+1)))) (treeHash (cs++[y]) H (2*(n >>> (H+1))+1))
        rw [hkeySib]
        congr 1
        · have hbound : (2*(n >>> (H+1)) + 1) * 2^H ≤ cs.length := by
            rw [hcs, ← hkey]; exact hboundOld
          exact (treeHash_ext cs [y] H (2*(n >>> (H+1))) hbound).symm
        · rw [ihc, hkey]
      · intro h hh
        rw [hstep, hsnd]
        by_cases heq : h.val < H
        · exact ih1 h heq
        · have hval : h.val = H := by omega
          have hEq : h = (⟨H,hHlt⟩ : Fin 26) := Fin.ext hval
          subst hEq
          rw [hsubH]
          simp [hb]
      · intro h hh
        rw [hstep, hsnd]
        exact ih2 h (by omega)
    · -- store branch: the block at height `H` isn't complete yet -- `n`'s ancestor there
      -- becomes `subtrees`'s new value, padded with the zero hash above it.
      have hbf : Nat.testBit n H = false := by simpa using hb
      have hfst : (appendBody n (cur, sub) ⟨H, hHlt⟩).1 = H2 cur (Z H) := by
        show (if Nat.testBit n H then (H2 (sub ⟨H,hHlt⟩) cur, sub)
              else (H2 cur (Z H), Function.update sub ⟨H,hHlt⟩ cur)).1 = H2 cur (Z H)
        rw [if_neg (by simp [hbf])]
      have hsnd : (appendBody n (cur, sub) ⟨H, hHlt⟩).2 = Function.update sub ⟨H,hHlt⟩ cur := by
        show (if Nat.testBit n H then (H2 (sub ⟨H,hHlt⟩) cur, sub)
              else (H2 cur (Z H), Function.update sub ⟨H,hHlt⟩ cur)).2
              = Function.update sub ⟨H,hHlt⟩ cur
        rw [if_neg (by simp [hbf])]
      have hkey : n >>> H = 2 * (n >>> (H+1)) := by
        have hs := shiftRight_succ_eq n H
        have h2 : (n >>> H) % 2 ≠ 1 :=
          of_decide_eq_false ((testBit_shiftRight_eq n H).symm.trans hbf)
        omega
      have hlen : (cs++[y]).length = n+1 := by rw [← hcs]; simp
      have hzero : treeHash (cs++[y]) H (n>>>H+1) = Z H := by
        apply treeHash_zero
        rw [hlen]
        exact succ_le_shiftRight_succ_mul n H
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep, hfst]
        show H2 cur (Z H) = H2 (treeHash (cs++[y]) H (2*(n >>> (H+1)))) (treeHash (cs++[y]) H (2*(n >>> (H+1))+1))
        rw [ihc, hkey]
        congr 1
        rw [← hkey]
        exact hzero.symm
      · intro h hh
        rw [hstep, hsnd]
        by_cases heq : h = (⟨H,hHlt⟩ : Fin 26)
        · subst heq
          rw [Function.update_self, ihc]
          simp [hbf]
        · rw [Function.update_of_ne heq]
          have hlt : h.val < H := by
            rcases Nat.lt_or_ge h.val H with h1 | h1
            · exact h1
            · exact absurd (Fin.ext (by omega : h.val = H)) heq
          exact ih1 h hlt
      · intro h hh
        rw [hstep, hsnd]
        have hne : h ≠ (⟨H,hHlt⟩:Fin 26) := fun heq => hh (heq ▸ Nat.lt_succ_self H)
        rw [Function.update_of_ne hne]
        exact ih2 h (by omega)

/-- `appendFold_aux` at `H = 26`, restated with the bits of the new length (via
    `testBit_succ_cases`), as `foldAppend_spec` needs. -/
lemma appendEffects_root_subtrees (cs : List F) (hcap : cs.length < 2^26) (y : F)
    (subOld : Fin 26 → F)
    (hSubInv : ∀ h : Fin 26, Nat.testBit cs.length h.val = true →
        subOld h = treeHash cs h.val (siblingIdx cs.length h.val)) :
    (Fin.foldl 26 (appendBody cs.length) (y, subOld)).1 = treeHash (cs ++ [y]) 26 0
    ∧ ∀ h : Fin 26, Nat.testBit (cs.length+1) h.val = true →
        (Fin.foldl 26 (appendBody cs.length) (y, subOld)).2 h
          = treeHash (cs++[y]) h.val (siblingIdx (cs.length+1) h.val) := by
  set n := cs.length with hcs
  have hbridge : Fin.foldl 26 (appendBody n) (y, subOld) = foldUpTo (appendBodyN n) 26 (y, subOld) :=
    fin_foldl_eq_foldUpTo 26 (appendBody n) (y, subOld)
  obtain ⟨haux1, haux2, _⟩ := appendFold_aux n cs rfl y subOld hSubInv 26 (le_refl 26)
  have hn0 : n >>> 26 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hcap
  constructor
  · rw [hbridge, haux1, hn0]
  · intro h hSucc
    rw [hbridge]
    rcases testBit_succ_cases h.val n hSucc with ⟨hbt, hshift⟩ | ⟨hbf, hshift⟩
    · have hval : (foldUpTo (appendBodyN n) 26 (y, subOld)).2 h = subOld h :=
        haux2 h h.isLt |>.trans (if_pos hbt)
      rw [hval, hSubInv h hbt]
      have hidxEq : siblingIdx n h.val = siblingIdx (n+1) h.val := by
        unfold siblingIdx
        rw [if_pos hbt, if_pos hSucc, hshift]
      rw [hidxEq]
      symm
      apply treeHash_ext
      rw [← hcs, ← hidxEq]
      have hsib : siblingIdx n h.val = n >>> h.val - 1 := by unfold siblingIdx; rw [if_pos hbt]
      rw [hsib]
      have hb1 : 1 ≤ n >>> h.val := by
        have h2 : (n >>> h.val) % 2 = 1 :=
          of_decide_eq_true ((testBit_shiftRight_eq n h.val).symm.trans hbt)
        rcases Nat.eq_zero_or_pos (n >>> h.val) with h0 | h0
        · rw [h0] at h2; simp at h2
        · exact h0
      have heq2 : n >>> h.val - 1 + 1 = n >>> h.val := by omega
      rw [heq2]
      exact div_mul_le n h.val
    · have hval : (foldUpTo (appendBodyN n) 26 (y, subOld)).2 h
          = treeHash (cs++[y]) h.val (n >>> h.val) :=
        haux2 h h.isLt |>.trans (if_neg (by simp [hbf]))
      rw [hval]
      congr 1
      unfold siblingIdx
      rw [if_pos hSucc, hshift]
      generalize n >>> h.val = m
      omega

/-- `foldAppend cs initTree` (with `cs.length < 2^26`) is the expected tree: `nextIndex`
    is `cs.length`, `root` is the `treeHash` root, and every `subtrees` slot
    `appendEffects` reads holds the right completed block. -/
lemma foldAppend_spec : ∀ cs : List F, cs.length < 2^26 →
    (foldAppend cs initTree).nextIndex = cs.length
    ∧ (foldAppend cs initTree).root = treeHash cs 26 0
    ∧ ∀ h : Fin 26, Nat.testBit cs.length h.val = true →
        (foldAppend cs initTree).subtrees h = treeHash cs h.val (siblingIdx cs.length h.val) := by
  intro cs
  induction cs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨rfl, ?_, ?_⟩
    · show initTree.root = treeHash [] 26 0
      show Z 26 = treeHash [] 26 0
      exact (treeHash_zero [] 26 0 (by simp)).symm
    · intro h htb
      have hfalse : Nat.testBit 0 h.val = false := by simp
      simp [hfalse] at htb
  | append_singleton ys y ih =>
    intro hcap
    have hlenEq : (ys ++ [y]).length = ys.length + 1 := by simp
    have hcapY : ys.length < 2^26 := by rw [hlenEq] at hcap; omega
    obtain ⟨hNI, hRoot, hSub⟩ := ih hcapY
    have hT1 : foldAppend (ys++[y]) initTree = appendEffects y (foldAppend ys initTree) := by
      simp [foldAppend]
    obtain ⟨hR2, hS2⟩ := appendEffects_root_subtrees ys (hNI ▸ hcapY) y
      (foldAppend ys initTree).subtrees (hNI ▸ hSub)
    obtain ⟨hEr, hEs⟩ := appendEffects_eq y (foldAppend ys initTree)
    rw [hNI] at hEr hEs
    refine ⟨?_, ?_, ?_⟩
    · rw [hT1, hlenEq]
      show (foldAppend ys initTree).nextIndex + 1 = ys.length + 1
      rw [hNI]
    · rw [hT1, hEr, hR2]
    · intro h htb
      rw [hT1, hEs, hlenEq]
      rw [hlenEq] at htb
      exact hS2 h htb

-- HELPER: telescoping collision (like `H4` in invariant 2, but over 26 levels): if two
-- openings hash to the same root, either the leaves are equal or the first level where
-- they differ is an `H2` collision.

/-- `Opening.calcRoot`'s per-level combination step, as a function of the plain `ℕ`
    height. -/
def stepFn (k : ℕ) (sib : ℕ → F) : F → ℕ → F :=
  fun acc h => if Nat.testBit k h then H2 (sib h) acc else H2 acc (sib h)

/-- The `H2` input pair at height `h`, used to state an `H2Collision`. -/
def stepPair (k : ℕ) (sib : ℕ → F) (acc : F) (h : ℕ) : F × F :=
  if Nat.testBit k h then (sib h, acc) else (acc, sib h)

lemma stepFn_eq (k : ℕ) (sib : ℕ → F) (acc : F) (h : ℕ) :
    stepFn k sib acc h = H2 (stepPair k sib acc h).1 (stepPair k sib acc h).2 := by
  unfold stepFn stepPair
  split_ifs <;> rfl

lemma telescope (k : ℕ) (sib1 sib2 : ℕ → F) (leaf1 leaf2 : F) : ∀ H : ℕ,
    foldUpTo (stepFn k sib1) H leaf1 = foldUpTo (stepFn k sib2) H leaf2 →
    (leaf1 = leaf2 ∧ ∀ h, h < H → sib1 h = sib2 h)
    ∨ ∃ h, h < H ∧ H2Collision
        (stepPair k sib1 (foldUpTo (stepFn k sib1) h leaf1) h)
        (stepPair k sib2 (foldUpTo (stepFn k sib2) h leaf2) h)
  | 0, heq => Or.inl ⟨heq, fun h hh => absurd hh (by omega)⟩
  | (H+1), heq => by
      have step_eq : stepFn k sib1 (foldUpTo (stepFn k sib1) H leaf1) H
                   = stepFn k sib2 (foldUpTo (stepFn k sib2) H leaf2) H := heq
      rw [stepFn_eq, stepFn_eq] at step_eq
      by_cases hpair : stepPair k sib1 (foldUpTo (stepFn k sib1) H leaf1) H
                      = stepPair k sib2 (foldUpTo (stepFn k sib2) H leaf2) H
      · -- the two `H2` argument pairs at this level agree: descend to level `H` via the
        -- induction hypothesis, then extend the agreement by this level's siblings too.
        have hacc : foldUpTo (stepFn k sib1) H leaf1 = foldUpTo (stepFn k sib2) H leaf2
            ∧ sib1 H = sib2 H := by
          unfold stepPair at hpair
          split_ifs at hpair with hb
          · exact ⟨(Prod.ext_iff.mp hpair).2, (Prod.ext_iff.mp hpair).1⟩
          · exact ⟨(Prod.ext_iff.mp hpair).1, (Prod.ext_iff.mp hpair).2⟩
        rcases telescope k sib1 sib2 leaf1 leaf2 H hacc.1 with ⟨hL, hS⟩ | ⟨h0, hh0, hcol⟩
        · refine Or.inl ⟨hL, fun h hh => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh' | hh'
          · exact hS h hh'
          · rw [hh']; exact hacc.2
        · exact Or.inr ⟨h0, by omega, hcol⟩
      · -- the pairs disagree yet combined to the same `H2` output: a collision, right here.
        exact Or.inr ⟨H, by omega, ⟨hpair, step_eq⟩⟩

-- 7a. Extractability: a valid opening's leaf is what the tree holds at its index, or
-- there is an `H2` collision. Otherwise any path hashing to a real root would do.
-- Given:
  -- cs, with cs.length < 2^26
  -- O : Opening, valid for leaf c against (foldAppend cs initTree).root
-- Then: leafAt cs O.index = c (the zero leaf if unwritten), or an H2Collision.

/-- `O.siblings` as a plain `ℕ → F` (default `0` past height 26, never read). -/
def OpeningSib (O : Opening) : ℕ → F := fun h => if hh : h < 26 then O.siblings ⟨h,hh⟩ else 0

lemma calcRoot_eq_foldUpTo (O : Opening) (leaf : F) :
    O.calcRoot leaf = foldUpTo (stepFn O.index.val (OpeningSib O)) 26 leaf := by
  unfold Opening.calcRoot
  apply fin_foldl_eq_foldUpTo_plain
  intro x h hh
  unfold stepFn OpeningSib Opening.accIsRight
  rw [dif_pos hh]

theorem opening_extractable_or_collision
    (cs : List F) (hcap : cs.length < 2^26) (O : Opening) (c : F)
    (hValid : O.Valid c (foldAppend cs initTree).root) :
    leafAt cs O.index.val = c
    ∨ ∃ h : Fin 26, H2Collision
        (stepPair O.index.val (OpeningSib O)
          (foldUpTo (stepFn O.index.val (OpeningSib O)) h.val c) h.val)
        (stepPair O.index.val (OpeningSib (canonicalOpening cs O.index))
          (foldUpTo (stepFn O.index.val (OpeningSib (canonicalOpening cs O.index))) h.val
            (leafAt cs O.index.val)) h.val) := by
  have hRoot : (foldAppend cs initTree).root = treeHash cs 26 0 := (foldAppend_spec cs hcap).2.1
  have hCanon : (canonicalOpening cs O.index).calcRoot (leafAt cs O.index.val) = treeHash cs 26 0 :=
    calcRoot_canonicalOpening cs O.index
  -- Both `O` and the canonical opening of `O.index` fold to the same root; feed that to
  -- `telescope` to either extract the real leaf or exhibit the first colliding level.
  have hEq : foldUpTo (stepFn O.index.val (OpeningSib O)) 26 c
      = foldUpTo (stepFn O.index.val (OpeningSib (canonicalOpening cs O.index))) 26 (leafAt cs O.index.val) := by
    have e1 := calcRoot_eq_foldUpTo O c
    have e2 := calcRoot_eq_foldUpTo (canonicalOpening cs O.index) (leafAt cs O.index.val)
    rw [show (canonicalOpening cs O.index).index = O.index from rfl] at e2
    rw [← e1, ← e2]
    unfold Opening.Valid at hValid
    rw [hValid, hRoot, hCanon]
  rcases telescope O.index.val (OpeningSib O) (OpeningSib (canonicalOpening cs O.index)) c
      (leafAt cs O.index.val) 26 hEq with ⟨hL, _⟩ | ⟨h0, hh0, hcol⟩
  · exact Or.inl hL.symm
  · exact Or.inr ⟨⟨h0, hh0⟩, hcol⟩

-- 7b. Opening preservation: a deposited commitment keeps a valid opening (same index,
-- new siblings) however many commitments are appended later.
-- Given:
  -- c = cs[k] for some k < cs.length
  -- (cs ++ later), with (cs ++ later).length < 2^26
-- Then: some Opening O' with O'.index = k is valid for c against
--   (foldAppend (cs ++ later) initTree).root.
theorem opening_forward_preservation
    (cs later : List F) (k : ℕ) (hk : k < cs.length) (c : F) (hc : cs[k]'hk = c)
    (hcap : (cs ++ later).length < 2^26) :
    ∃ O' : Opening, O'.index.val = k ∧ O'.Valid c (foldAppend (cs++later) initTree).root := by
  have hlen : (cs++later).length = cs.length + later.length := by simp
  have hklt : k < 2^26 := by omega
  refine ⟨canonicalOpening (cs++later) ⟨k, hklt⟩, rfl, ?_⟩
  have h1 := calcRoot_canonicalOpening (cs++later) ⟨k, hklt⟩
  have h2 : leafAt (cs++later) k = c := by
    rw [leafAt_append_left cs later k hk]
    unfold leafAt
    rw [dif_pos hk]
    exact hc
  have h3 := (foldAppend_spec (cs++later) hcap).2.1
  show (canonicalOpening (cs++later) ⟨k, hklt⟩).calcRoot c = (foldAppend (cs++later) initTree).root
  rw [← h2, h1, ← h3]

-- 7c. A spend's claimed index for a non-zero input really holds that input's
-- commitment, or there is an `H2` collision. So a prover can't evade the nullifier check
-- (invariant 2, level 3) by claiming another index for an already-spent note.
-- Given:
  -- RelationS pubInputs witness, with witness.inAmt i ≠ 0
  -- cs, with cs.length < 2^26, and pubInputs.R = (foldAppend cs initTree).root
-- Then: cs[(witness.openings i).index] = witness.inC i, or an H2Collision.
theorem witness_opening_is_genuine_or_collision
    (witness : Witness) (pubInputs : PubInputs) (cs : List F) (hcap : cs.length < 2^26)
    (hRel : RelationS pubInputs witness) (i : Fin 2) (hne : witness.inAmt i ≠ 0)
    (hR : pubInputs.R = (foldAppend cs initTree).root) :
    leafAt cs (witness.openings i).index.val = witness.inC i
    ∨ ∃ h : Fin 26, H2Collision
        (stepPair (witness.openings i).index.val (OpeningSib (witness.openings i))
          (foldUpTo (stepFn (witness.openings i).index.val (OpeningSib (witness.openings i)))
            h.val (witness.inC i)) h.val)
        (stepPair (witness.openings i).index.val
          (OpeningSib (canonicalOpening cs (witness.openings i).index))
          (foldUpTo (stepFn (witness.openings i).index.val
            (OpeningSib (canonicalOpening cs (witness.openings i).index))) h.val
            (leafAt cs (witness.openings i).index.val)) h.val) := by
  have hValid : (witness.openings i).Valid (witness.inC i) pubInputs.R := hRel.correctOpenings i hne
  rw [hR] at hValid
  exact opening_extractable_or_collision cs hcap (witness.openings i) (witness.inC i) hValid

-- 7d. Strengthens 6b: from a reachable world, every non-zero input of a successful
-- `transact` was really deposited at its claimed index, or there is an `H2` collision.
-- Given:
  -- an old_world, reachable from initWorld
  -- a new_world
-- When: transact
-- Then: (as 6b) plus a list cs with pubInputs.R = (foldAppend cs initTree).root, where
--   each non-zero input's claimed index holds its commitment -- or an H2Collision.
theorem transact_implies_deposited_openings
    (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ)
    (oldWorld newWorld: World)
    (hReach : ReachableWorld (initWorld cfg balances rentExemptMin) oldWorld)
    (inputs: TxInputs) (h1: transact inputs oldWorld newWorld) :
    ∃ witness, RelationS inputs.pubInputs witness
      ∧ ∃ cs : List F, inputs.R = (foldAppend cs initTree).root
      ∧ ∀ i, witness.inAmt i ≠ 0 →
          leafAt cs (witness.openings i).index.val = witness.inC i
          ∨ ∃ h : Fin 26, H2Collision
              (stepPair (witness.openings i).index.val (OpeningSib (witness.openings i))
                (foldUpTo (stepFn (witness.openings i).index.val (OpeningSib (witness.openings i)))
                  h.val (witness.inC i)) h.val)
              (stepPair (witness.openings i).index.val
                (OpeningSib (canonicalOpening cs (witness.openings i).index))
                (foldUpTo (stepFn (witness.openings i).index.val
                  (OpeningSib (canonicalOpening cs (witness.openings i).index))) h.val
                  (leafAt cs (witness.openings i).index.val)) h.val) := by
  obtain ⟨witness, hRel, hRknown, _⟩ := transact_implies_valid_openings oldWorld newWorld inputs h1
  rcases history_entries_are_genuine_roots cfg balances rentExemptMin oldWorld hReach inputs.R hRknown
    with hZ | h0 | ⟨cs, hcslt, hcs⟩
  · exact ⟨witness, hRel, [], by rw [hZ]; rfl, fun i hne =>
      witness_opening_is_genuine_or_collision witness inputs.pubInputs [] (by norm_num) hRel i hne
        (by show inputs.R = (foldAppend [] initTree).root; rw [hZ]; rfl)⟩
  · exact absurd h0 h1.1.knownRoot.2
  · exact ⟨witness, hRel, cs, hcs, fun i hne =>
      witness_opening_is_genuine_or_collision witness inputs.pubInputs cs hcslt hRel i hne hcs⟩

-- 8. Note value consistency: a spender can't change a note's value. If a spend's input
-- commitment equals an earlier output commitment, both witnesses open it to the same
-- (amount, pubkey, blinding, mint), or there is an `H4` collision.
-- Given:
  -- witness1 satisfying RelationS for pubInput1
  -- witness2's input i has the same commitment as witness1's output j
-- Then: witness2's (inAmt, inPk, inR, mint) at i = witness1's (outAmt, outPk, outR, mint)
-- at j -- or an H4Collision between those two tuples.
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

-- 9. Proof binding: a valid proof can't be resubmitted with different TxInputs (e.g. a
-- new recipient or fee) unless an IC relation or a sha256 collision is found.

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

-- 9b. Protocol level: the same proof can't be used for different TxInputs, unless an
-- IC relation or a sha256 collision is found.
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

-- 10. Unspent notes can always be spent, unless a real protocol check blocks it (pool or
-- signer insolvency, a full tree, or the root leaving the 100-root history). So every
-- non-ZKP precondition is a hypothesis, and we show the proof is never the obstacle:
-- `Deployment.completeness` gives a proof that makes `transact` succeed.
-- The input openings are derived from a real earlier deposit (7b), not assumed. The
-- other `RelationS` fields (nullifiers, outputs, amounts) are still hypotheses.
-- Given:
  -- an old_world
  -- witness's non-zero inputs were deposited in cs0, with `later` appended since
  --   (inputs.R = (foldAppend (cs0 ++ later) initTree).root)
  -- witness's other RelationS fields
-- When: (all other transact preconditions hold)
-- Then: some Groth16 proof makes transact go through.
theorem unspent_note_is_spendable
  (oldWorld: World) (inputs: TxInputs) (witness: Witness)
  (cs0 later : List F) (hcap : (cs0 ++ later).length < 2^26)
  (hR : inputs.R = (foldAppend (cs0 ++ later) initTree).root)
  (hDeposited : ∀ i, witness.inAmt i ≠ 0 →
      (witness.openings i).index.val < cs0.length
      ∧ leafAt cs0 (witness.openings i).index.val = witness.inC i)
  (hOutputCommitmentIntegrity : ∀ j, inputs.pubInputs.outCommitments j
      = commit (witness.outAmt j) (witness.outPk j) (witness.outR j) witness.mint)
  (hNullifierCorrectness : ∀ i, inputs.pubInputs.nullifiers i
      = nullifier (witness.inC i) (witness.sign i) (witness.openings i).index)
  (hNoDuplicateNullifiers : inputs.pubInputs.nullifiers 0 ≠ inputs.pubInputs.nullifiers 1)
  (hAmountConservation : witness.inAmt 0 + witness.inAmt 1 + inputs.pubInputs.pubAmt
      = witness.outAmt 0 + witness.outAmt 1)
  (hOutputRangeChecks : ∀ j, (witness.outAmt j).val < 2^248)
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
  classical
  -- For each spent input, invoke invariant 7b to get a genuinely valid opening at the
  -- same claimed index, against the *current* root `inputs.R` (not just `cs0`'s).
  have hOpen : ∀ i : Fin 2, witness.inAmt i ≠ 0 → ∃ O' : Opening,
      O'.index = (witness.openings i).index ∧ O'.Valid (witness.inC i) inputs.R := by
    intro i hne
    obtain ⟨hlt, heq⟩ := hDeposited i hne
    have hc : cs0[(witness.openings i).index.val]'hlt = witness.inC i := by
      have hh := heq
      unfold leafAt at hh
      rwa [dif_pos hlt] at hh
    obtain ⟨O', hidx, hvalid⟩ :=
      opening_forward_preservation cs0 later (witness.openings i).index.val hlt (witness.inC i) hc hcap
    exact ⟨O', Fin.ext hidx, by rw [hR]; exact hvalid⟩
  -- `witness'`: `witness` with each non-zero input's opening replaced by the one just
  -- derived -- same claimed index, so everything computed from the index (nullifier,
  -- signature) is unaffected; only the siblings, previously a bare hypothesis, change.
  set witness' : Witness := { witness with
    openings := fun i => if h : witness.inAmt i ≠ 0 then Classical.choose (hOpen i h) else witness.openings i
  } with hwitness'_def
  have hIdxEq : ∀ i, (witness'.openings i).index = (witness.openings i).index := by
    intro i
    by_cases h : witness.inAmt i ≠ 0
    · show (if h' : witness.inAmt i ≠ 0 then Classical.choose (hOpen i h') else witness.openings i).index
        = (witness.openings i).index
      rw [dif_pos h]
      exact (Classical.choose_spec (hOpen i h)).1
    · show (if h' : witness.inAmt i ≠ 0 then Classical.choose (hOpen i h') else witness.openings i).index
        = (witness.openings i).index
      rw [dif_neg h]
  have hSignEq : ∀ i, witness'.sign i = witness.sign i := by
    intro i
    show signature (witness.inSk i) (witness.inC i) (witness'.openings i).index
       = signature (witness.inSk i) (witness.inC i) (witness.openings i).index
    rw [hIdxEq]
  have hRel' : RelationS inputs.pubInputs witness' := {
    outputCommitmentIntegrity := hOutputCommitmentIntegrity
    nullifierCorrectness := fun i => by
      show inputs.pubInputs.nullifiers i
        = nullifier (witness.inC i) (witness'.sign i) (witness'.openings i).index
      rw [hSignEq, hIdxEq]
      exact hNullifierCorrectness i
    noDuplicateNullifiers := hNoDuplicateNullifiers
    correctOpenings := fun i hne => by
      have hne' : witness.inAmt i ≠ 0 := hne
      show (witness'.openings i).Valid (witness.inC i) inputs.R
      show (if h' : witness.inAmt i ≠ 0 then Classical.choose (hOpen i h') else witness.openings i).Valid
        (witness.inC i) inputs.R
      rw [dif_pos hne']
      exact (Classical.choose_spec (hOpen i hne')).2
    amountConservation := hAmountConservation
    outputRangeChecks := hOutputRangeChecks
  }
  obtain ⟨π, hπ⟩ := Deployment.completeness inputs.pubInputs witness' hRel'
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

-- 11. Config and rent-exempt minimum never change. This holds only because `transact` is
-- the only operation modeled; the authority-gated config update is not modeled, so
-- nothing is claimed about it.

-- Proof for a single step executing transact.
-- Given:
  -- an old_world
  -- a new_world
-- When: transact
-- Then: new_world.state.config = old_world.state.config
--   ∧ new_world.rentExemptMin = old_world.rentExemptMin
lemma config_and_rent_exempt_min_step
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h: transact inputs oldWorld newWorld)
  : newWorld.state.config = oldWorld.state.config
    ∧ newWorld.rentExemptMin = oldWorld.rentExemptMin := by
  obtain ⟨_, heff⟩ := h
  refine ⟨?_, ?_⟩
  · rw [heff.config]; unfold transactEffects transferEffects; split_ifs <;> rfl
  · rw [heff.rentExemptMin]; unfold transactEffects transferEffects; split_ifs <;> rfl

-- Induction over reachable worlds: both stay as `initWorld` set them.
theorem config_and_rent_exempt_min_constant
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : w.state.config = cfg ∧ w.rentExemptMin = rentExemptMin := by
  induction h with
  | noStep => exact ⟨rfl, rfl⟩
  | extend inputs _ transact_proof ih =>
    obtain ⟨ihc, ihr⟩ := ih
    obtain ⟨hc, hr⟩ := config_and_rent_exempt_min_step _ _ inputs transact_proof
    exact ⟨hc.trans ihc, hr.trans ihr⟩

-- 12. Recipient and fee-recipient balances change by exactly what `transact` pays them
-- (the `balances` counterpart of invariant 3). Assumes recipient, fee recipient and
-- signer are distinct; otherwise `AgreesOnProgramEffects.payees` doesn't fix the result.
-- The signer's own balance on a deposit is unconstrained (see the TODO(security gap) on
-- `AgreesOnProgramEffects`). Single-step only; a multi-step version is future work.

-- 12a. One step adds exactly `f` to the fee recipient (assuming `t ≠ s` and `A ≠ t`).
-- Given:
  -- an old_world
  -- a new_world
  -- inputs.t ≠ inputs.s and inputs.A ≠ inputs.t
-- When: transact
-- Then: new_world.balances inputs.t = old_world.balances inputs.t + inputs.f
theorem fee_recipient_balance_correctness
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h1: transact inputs oldWorld newWorld)
  (hts: inputs.t ≠ inputs.s)
  (hAt: inputs.A ≠ inputs.t)
  : newWorld.balances inputs.t = oldWorld.balances inputs.t + inputs.f := by
  obtain ⟨_, heff⟩ := h1
  rw [heff.payees inputs.t (Or.inr rfl) hts]
  unfold transactEffects
  simp only [Function.update_self]
  congr 1
  unfold transferEffects
  split_ifs with hz hpos
  · rfl
  · exact Function.update_of_ne hts _ _
  · exact Function.update_of_ne hAt.symm _ _

-- 12b. One withdrawal adds exactly `|extAmt|` to the recipient (assuming `A ≠ s` and
-- `A ≠ t`).
-- Given:
  -- an old_world
  -- a new_world
  -- inputs.extAmt < 0, inputs.A ≠ inputs.s and inputs.A ≠ inputs.t
-- When: transact
-- Then: new_world.balances inputs.A = old_world.balances inputs.A + inputs.extAmt.natAbs
theorem withdrawal_recipient_balance_correctness
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h1: transact inputs oldWorld newWorld)
  (hWithdrawal: inputs.extAmt < 0)
  (hAs: inputs.A ≠ inputs.s)
  (hAt: inputs.A ≠ inputs.t)
  : newWorld.balances inputs.A = oldWorld.balances inputs.A + inputs.extAmt.natAbs := by
  obtain ⟨_, heff⟩ := h1
  rw [heff.payees inputs.A (Or.inl rfl) hAs]
  unfold transactEffects
  simp only [Function.update_of_ne hAt]
  unfold transferEffects
  split_ifs with hz hpos
  · exfalso; omega
  · exfalso; omega
  · exact Function.update_self _ _ _

-- 13. Value conservation (no inflation). Invariant 3 tracks external SOL only; this
-- tracks the private notes: `solBalance` = rent reserve + value created as outputs −
-- value spent as inputs. So nobody withdraws more than was deposited, or spends a note
-- for more than its value. Holds unless an `H2Collision`, `H4Collision` or
-- `H4ZeroPreimage` is found.
-- Idealizing assumption (a): each step's `extAmt` and `f` are below `2^248` (true for any
-- u64/i64). With that, field wrap-around within a step is ruled out by proof
-- (`value_delta_eq_ext_sub_fee`), not assumed.

-- HELPER: a zero input is trivially bounded, so the `≠ 0` hypothesis can be dropped.
lemma inAmt_val_bound (witness : Witness)
    (hInBound : ∀ i, witness.inAmt i ≠ 0 → (witness.inAmt i).val < 2^248) :
    ∀ i, (witness.inAmt i).val < 2^248 := by
  intro i
  by_cases h : witness.inAmt i = 0
  · rw [h, ZMod.val_zero]; exact Nat.two_pow_pos 248
  · exact hInBound i h

-- HELPER: an `F` equation between integers is an integer equation when their difference
-- is below `p`.
lemma zmod_eq_iff_int_eq (a b : ℤ) (hbound : |a - b| < (p:ℤ)) (heq : (a : F) = (b : F)) :
    a = b := by
  have hdvd : (p:ℤ) ∣ (a - b) := (ZMod.intCast_eq_intCast_iff_dvd_sub b a p).mp heq.symm
  have := Int.eq_zero_of_abs_lt_dvd hdvd hbound
  omega

-- 13, stage 1. Single step, in ℤ: output value − input value = extAmt − f (lifting
-- `amountConservation` from `F`). Inputs are assumed bounded here; stage 3 proves it.
-- Given:
  -- witness satisfying RelationS for pubInputs
  -- pubInputs.pubAmt consistent with extAmt, f (pubAmtConsistent)
  -- witness's nonzero inputs bounded by 2^248 (hInBound)
  -- extAmt, f individually bounded by 2^248 (idealizing assumption (a) above)
-- Then: (outAmt 0).val + (outAmt 1).val - (inAmt 0).val - (inAmt 1).val = extAmt - f, in ℤ.
theorem value_delta_eq_ext_sub_fee
    (witness : Witness) (pubInputs : PubInputs) (extAmt : ℤ) (f : ℕ)
    (hRel : RelationS pubInputs witness)
    (hPubAmt : pubAmtConsistent extAmt f pubInputs.pubAmt)
    (hInBound : ∀ i, witness.inAmt i ≠ 0 → (witness.inAmt i).val < 2^248)
    (hExtBound : extAmt.natAbs < 2^248) (hFeeBound : f < 2^248) :
    ((witness.outAmt 0).val : ℤ) + (witness.outAmt 1).val
      - (witness.inAmt 0).val - (witness.inAmt 1).val = extAmt - f := by
  have hInVal := inAmt_val_bound witness hInBound
  have hi0 := hInVal 0
  have hi1 := hInVal 1
  have ho0 := hRel.outputRangeChecks 0
  have ho1 := hRel.outputRangeChecks 1
  -- The `F`-level identity this whole lemma is really about: rearranging
  -- `amountConservation` with `pubAmt = extAmt - f` substituted in.
  have hFeq : witness.inAmt 0 + witness.inAmt 1 + (extAmt : F)
      = witness.outAmt 0 + witness.outAmt 1 + (f : F) := by
    have hAC := hRel.amountConservation
    rw [hPubAmt.2.2] at hAC
    linear_combination hAC
  -- Lift both sides to their `ℤ` counterparts via `.val`, then to `F` again to match `hFeq`.
  set L : ℤ := (witness.inAmt 0).val + (witness.inAmt 1).val + extAmt with hLdef
  set R : ℤ := (witness.outAmt 0).val + (witness.outAmt 1).val + (f : ℤ) with hRdef
  have hLF : (L : F) = witness.inAmt 0 + witness.inAmt 1 + (extAmt : F) := by
    rw [hLdef]; push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hRF : (R : F) = witness.outAmt 0 + witness.outAmt 1 + (f : F) := by
    rw [hRdef]; push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hLReq : (L : F) = (R : F) := by rw [hLF, hRF]; exact hFeq
  -- Both sides are far below `p` (~2^254), so the `F` equation is a `ℤ` equation.
  have hp_lt : (2:ℤ)^250 < (p:ℤ) := by norm_num [p]
  have hbound : |L - R| < (p:ℤ) := by
    rw [abs_lt]
    constructor <;> [skip; skip] <;>
      · have := hp_lt
        omega
  have hLR := zmod_eq_iff_int_eq L R hbound hLReq
  rw [hLdef, hRdef] at hLR
  omega

-- 13, stage 2. `tree_well_formed`, plus: every leaf is a commitment with amount below
-- `2^248` (each leaf was an output, and `outputRangeChecks` bounds outputs).
theorem tree_well_formed_bounded
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : ∃ cs: List F, w.state.tree = foldAppend cs initTree ∧
      ∀ x ∈ cs, ∃ amt pk r mint, x = commit amt pk r mint ∧ amt.val < 2^248 := by
  induction h with
  | noStep => exact ⟨[], rfl, fun x hx => by simp at hx⟩
  | extend inputs _ transact_proof ih =>
    obtain ⟨cs, hcs, hbound⟩ := ih
    obtain ⟨witness, hRel⟩ := (transact_requires_valid_proof_and_witness _ _ inputs).2 transact_proof
    obtain ⟨_, hagree⟩ := transact_proof
    refine ⟨cs ++ [inputs.outC0, inputs.outC1], ?_, ?_⟩
    · rw [hagree.tree]
      simp only [transactEffects, transferEffects_tree, foldAppend, List.foldl_append,
        List.foldl_cons, List.foldl_nil, hcs]
    · intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact hbound x hx
      · simp at hx
        rcases hx with hx | hx
        · subst hx
          have h0 := hRel.outputCommitmentIntegrity 0
          simp [TxInputs.pubInputs] at h0
          exact ⟨witness.outAmt 0, witness.outPk 0, witness.outR 0, witness.mint, h0,
            hRel.outputRangeChecks 0⟩
        · subst hx
          have h1 := hRel.outputCommitmentIntegrity 1
          simp [TxInputs.pubInputs] at h1
          exact ⟨witness.outAmt 1, witness.outPk 1, witness.outR 1, witness.mint, h1,
            hRel.outputRangeChecks 1⟩

-- 13, stage 2 continued. The same bound for the list behind each history root (as in
-- `history_entries_are_genuine_roots`).
theorem history_root_cs_bounded
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World)
  (h: ReachableWorld (initWorld cfg balances rentExemptMin) w)
  : ∀ R ∈ Set.range w.state.tree.history,
      R = Z 26 ∨ R = 0 ∨ ∃ cs: List F, cs.length < 2^26 ∧ R = (foldAppend cs initTree).root ∧
        ∀ x ∈ cs, ∃ amt pk r mint, x = commit amt pk r mint ∧ amt.val < 2^248 := by
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
    obtain ⟨witness, hRel⟩ := (transact_requires_valid_proof_and_witness _ _ inputs).2 transact_proof
    obtain ⟨hpre, hagree⟩ := transact_proof
    rw [hagree.tree] at hR
    simp only [transactEffects, transferEffects_tree] at hR
    rw [appendEffects_history] at hR
    rcases mem_range_update_or_mem_range _ _ _ _ hR with hEq | hR'
    · obtain ⟨cs, hcs, hbound⟩ := tree_well_formed_bounded cfg balances rentExemptMin _ h2
      have hcslt : cs.length < 2^26 - 2 := by
        have hroom := hpre.treeNotFull
        unfold treeHasRoom at hroom
        rw [hcs, foldAppend_nextIndex cs] at hroom
        exact hroom
      have hlen2 : (cs ++ [inputs.outC0, inputs.outC1]).length < 2^26 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      refine Or.inr (Or.inr ⟨cs ++ [inputs.outC0, inputs.outC1], hlen2, ?_, ?_⟩)
      · have : foldAppend (cs ++ [inputs.outC0, inputs.outC1]) initTree
            = appendEffects inputs.outC1 (appendEffects inputs.outC0 (foldAppend cs initTree)) := by
          simp [foldAppend]
        rw [this, ← hcs]
        exact hEq
      · intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hbound x hx
        · simp at hx
          rcases hx with hx | hx
          · subst hx
            have h0 := hRel.outputCommitmentIntegrity 0
            simp [TxInputs.pubInputs] at h0
            exact ⟨witness.outAmt 0, witness.outPk 0, witness.outR 0, witness.mint, h0,
              hRel.outputRangeChecks 0⟩
          · subst hx
            have h1 := hRel.outputCommitmentIntegrity 1
            simp [TxInputs.pubInputs] at h1
            exact ⟨witness.outAmt 1, witness.outPk 1, witness.outR 1, witness.mint, h1,
              hRel.outputRangeChecks 1⟩
    rw [appendEffects_history] at hR'
    rcases mem_range_update_or_mem_range _ _ _ _ hR' with hEq | hR''
    · obtain ⟨cs, hcs, hbound⟩ := tree_well_formed_bounded cfg balances rentExemptMin _ h2
      have hcslt : cs.length < 2^26 - 2 := by
        have hroom := hpre.treeNotFull
        unfold treeHasRoom at hroom
        rw [hcs, foldAppend_nextIndex cs] at hroom
        exact hroom
      have hlen1 : (cs ++ [inputs.outC0]).length < 2^26 := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      refine Or.inr (Or.inr ⟨cs ++ [inputs.outC0], hlen1, ?_, ?_⟩)
      · have : foldAppend (cs ++ [inputs.outC0]) initTree
            = appendEffects inputs.outC0 (foldAppend cs initTree) := by
          simp [foldAppend]
        rw [this, ← hcs]
        exact hEq
      · intro x hx
        rw [List.mem_append] at hx
        rcases hx with hx | hx
        · exact hbound x hx
        · simp at hx
          subst hx
          have h0 := hRel.outputCommitmentIntegrity 0
          simp [TxInputs.pubInputs] at h0
          exact ⟨witness.outAmt 0, witness.outPk 0, witness.outR 0, witness.mint, h0,
            hRel.outputRangeChecks 0⟩
    · exact ih R hR''

-- HELPER: the ways stage 3 can fail for input `i`: an H2 collision, an H4 collision, or
-- an H4 zero preimage.
def InputBreak (witness : Witness) (i : Fin 2) : Prop :=
  (∃ cs : List F, ∃ h : Fin 26, H2Collision
      (stepPair (witness.openings i).index.val (OpeningSib (witness.openings i))
        (foldUpTo (stepFn (witness.openings i).index.val (OpeningSib (witness.openings i)))
          h.val (witness.inC i)) h.val)
      (stepPair (witness.openings i).index.val
        (OpeningSib (canonicalOpening cs (witness.openings i).index))
        (foldUpTo (stepFn (witness.openings i).index.val
          (OpeningSib (canonicalOpening cs (witness.openings i).index))) h.val
          (leafAt cs (witness.openings i).index.val)) h.val))
  ∨ (∃ amt pk r mint, H4Collision
      (witness.inAmt i, witness.inPk i, witness.inR i, witness.mint) (amt, pk, r, mint))
  ∨ H4ZeroPreimage (witness.inAmt i, witness.inPk i, witness.inR i, witness.mint)

-- 13, stage 3. A non-zero input's amount is below `2^248`, inherited from the output
-- that created it (7c + stage 2 + `commitment_determines_value_or_collision`), or
-- `InputBreak`: a forged opening (H2), a wrong value (H4), or an unwritten leaf (H4 zero
-- preimage).
theorem input_value_bound_or_break
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ)
  (oldWorld: World) (inputs: TxInputs) (witness: Witness)
  (hReach : ReachableWorld (initWorld cfg balances rentExemptMin) oldWorld)
  (hRel : RelationS inputs.pubInputs witness)
  (hRootKnown : rootKnown oldWorld.state.tree inputs.R)
  (i : Fin 2) (hne : witness.inAmt i ≠ 0) :
  (witness.inAmt i).val < 2^248 ∨ InputBreak witness i := by
  rcases history_root_cs_bounded cfg balances rentExemptMin oldWorld hReach inputs.R hRootKnown.1
    with hZ | h0 | ⟨cs, hcslt, hcs, hbound⟩
  · -- The untouched empty tree: R = Z 26 = (foldAppend [] initTree).root, i.e. cs = [].
    -- Every claimed opening index is then "unwritten" (idx ≥ [].length = 0), so 7a/7c's
    -- genuine disjunct forces `witness.inC i = 0` -- the H4ZeroPreimage case.
    have hR0 : inputs.pubInputs.R = (foldAppend ([]:List F) initTree).root := by
      show inputs.R = _; rw [hZ]; rfl
    rcases witness_opening_is_genuine_or_collision witness inputs.pubInputs [] (by norm_num)
        hRel i hne hR0 with hgen | hcol
    · have hZ0 : leafAt ([]:List F) (witness.openings i).index.val = 0 := by
        simp [leafAt, Z]
      rw [hZ0] at hgen
      refine Or.inr (Or.inr (Or.inr ⟨?_⟩))
      show H4 (witness.inAmt i) (witness.inPk i) (witness.inR i) witness.mint = 0
      exact hgen.symm
    · exact Or.inr (Or.inl ⟨[], hcol⟩)
  · exact absurd h0 hRootKnown.2
  · have hRcs : inputs.pubInputs.R = (foldAppend cs initTree).root := by
      show inputs.R = _; rw [hcs]
    rcases witness_opening_is_genuine_or_collision witness inputs.pubInputs cs hcslt
        hRel i hne hRcs with hgen | hcol
    · by_cases hidx : (witness.openings i).index.val < cs.length
      · -- Genuinely-written leaf: it's some earlier output's commitment, and
        -- `outputRangeChecks` bounded that output when it was created.
        unfold leafAt at hgen
        rw [dif_pos hidx] at hgen
        have hmem : cs[(witness.openings i).index.val]'hidx ∈ cs := List.getElem_mem hidx
        obtain ⟨amt, pk, r, mint, heq, hb⟩ := hbound _ hmem
        have hCommitEq : commit (witness.inAmt i) (witness.inPk i) (witness.inR i) witness.mint
            = commit amt pk r mint := hgen.symm.trans heq
        rcases commitment_determines_value_or_collision _ _ _ _ _ _ _ _ hCommitEq
            with hTuple | hH4
        · refine Or.inl ?_
          have hAmtEq : witness.inAmt i = amt := by
            simp only [Prod.mk.injEq] at hTuple
            exact hTuple.1
          rw [hAmtEq]; exact hb
        · exact Or.inr (Or.inr (Or.inl ⟨amt, pk, r, mint, hH4⟩))
      · -- Unwritten leaf: the only genuine value is the zero-padding constant.
        have hZ0 : leafAt cs (witness.openings i).index.val = 0 := by
          unfold leafAt
          rw [dif_neg hidx]
          simp [Z]
        rw [hZ0] at hgen
        refine Or.inr (Or.inr (Or.inr ⟨?_⟩))
        show H4 (witness.inAmt i) (witness.inPk i) (witness.inR i) witness.mint = 0
        exact hgen.symm
    · exact Or.inr (Or.inl ⟨cs, hcol⟩)

-- 13, stage 4. One step from a reachable world: the stage 1 identity holds, or an input
-- hits `InputBreak` (stage 3).
theorem transact_value_delta_or_break
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ)
  (oldWorld newWorld: World) (inputs: TxInputs) (witness: Witness)
  (hReach : ReachableWorld (initWorld cfg balances rentExemptMin) oldWorld)
  (h1 : transact inputs oldWorld newWorld)
  (hRel : RelationS inputs.pubInputs witness)
  (hExtBound : inputs.extAmt.natAbs < 2^248) (hFeeBound : inputs.f < 2^248) :
  (((witness.outAmt 0).val : ℤ) + (witness.outAmt 1).val
      - (witness.inAmt 0).val - (witness.inAmt 1).val = inputs.extAmt - inputs.f)
  ∨ InputBreak witness 0 ∨ InputBreak witness 1 := by
  have hRootKnown := h1.1.knownRoot
  have hb0 : (witness.inAmt 0).val < 2^248 ∨ InputBreak witness 0 := by
    by_cases h0 : witness.inAmt 0 = 0
    · left; rw [h0, ZMod.val_zero]; exact Nat.two_pow_pos 248
    · exact input_value_bound_or_break cfg balances rentExemptMin oldWorld inputs witness
        hReach hRel hRootKnown 0 h0
  have hb1 : (witness.inAmt 1).val < 2^248 ∨ InputBreak witness 1 := by
    by_cases h1' : witness.inAmt 1 = 0
    · left; rw [h1', ZMod.val_zero]; exact Nat.two_pow_pos 248
    · exact input_value_bound_or_break cfg balances rentExemptMin oldWorld inputs witness
        hReach hRel hRootKnown 1 h1'
  rcases hb0 with hb0 | hbr0
  · rcases hb1 with hb1 | hbr1
    · exact Or.inl (value_delta_eq_ext_sub_fee witness inputs.pubInputs inputs.extAmt inputs.f
        hRel h1.1.pubAmtConsistency (fun i _ => by fin_cases i <;> assumption)
        hExtBound hFeeBound)
    · exact Or.inr (Or.inr hbr1)
  · exact Or.inr (Or.inl hbr0)

-- 13, stage 5 (final). For the trace `txs` actually applied since `initWorld`, with
-- assumption (a) on every step, there is one witness per transaction (`steps.map
-- Prod.fst = txs`) such that either `solBalance` = rent reserve + Σ (outputs − inputs)
-- over all steps, or some step hit `InputBreak`.
theorem value_conservation
  (cfg: config) (balances: Pubkey → ℕ) (rentExemptMin: ℕ) (w: World) (txs: List TxInputs)
  (h: ReachableTrace (initWorld cfg balances rentExemptMin) txs w)
  (hBound: ∀ tx ∈ txs, tx.extAmt.natAbs < 2^248 ∧ tx.f < 2^248)
  : ∃ steps : List (TxInputs × Witness),
      steps.map Prod.fst = txs ∧
      (∀ p ∈ steps, RelationS p.1.pubInputs p.2) ∧
      ((w.state.solBalance : ℤ) = steps.foldl (fun acc p =>
          acc + (((p.2.outAmt 0).val : ℤ) + (p.2.outAmt 1).val
            - (p.2.inAmt 0).val - (p.2.inAmt 1).val)) (rentExemptMin : ℤ)
        ∨ ∃ p ∈ steps, InputBreak p.2 0 ∨ InputBreak p.2 1) := by
  induction h with
  | noStep => exact ⟨[], rfl, fun p hp => by simp at hp, Or.inl (by simp [initWorld])⟩
  | @extend _ _ txs inputs h2 transact_proof ih =>
    obtain ⟨hExt, hFee⟩ := hBound inputs (List.mem_append_right _ (List.mem_singleton_self _))
    obtain ⟨steps, hsteps, hstepsRel, hsum⟩ :=
      ih (fun tx htx => hBound tx (List.mem_append_left _ htx))
    obtain ⟨witness, hRel⟩ := (transact_requires_valid_proof_and_witness _ _ inputs).2 transact_proof
    have hstep := transact_value_delta_or_break cfg balances rentExemptMin _ _ inputs witness
      h2.toReachableWorld transact_proof hRel hExt hFee
    have hsolstep := sol_balance_correctness_step _ _ inputs transact_proof
    refine ⟨steps ++ [(inputs, witness)], by simp [hsteps], ?_, ?_⟩
    · intro p hp
      rw [List.mem_append] at hp
      rcases hp with hp | hp
      · exact hstepsRel p hp
      · simp at hp; rw [hp]; exact hRel
    · rcases hsum with hsumClean | hsumBreak
      · rcases hstep with hstepClean | hstepBreak
        · left
          simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
          omega
        · exact Or.inr ⟨(inputs, witness), List.mem_append.mpr (Or.inr (by simp)), hstepBreak⟩
      · obtain ⟨p, hp, hbr⟩ := hsumBreak
        exact Or.inr ⟨p, List.mem_append.mpr (Or.inl hp), hbr⟩

end LeanSpec
