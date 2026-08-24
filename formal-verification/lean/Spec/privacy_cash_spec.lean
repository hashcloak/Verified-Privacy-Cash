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

  -- collision resistance of poseidon

  -- H1 : F → F has equal-cardinality domain and codomain, so asserting it is
  -- globally injective is consistent. H2/H3/H4 map into F from a strictly
  -- larger finite domain (F×F, F×F×F, F×F×F×F), so global injectivity is
  -- mathematically impossible by pigeonhole (|domain| > |F| = |codomain|):
  h_H1: ∀ (x y: F), H1 x = H1 y → x = y

class Sha where
  sha256: Bytes → BitVec 256

/-
Collision resistance / preimage resistance, relativized to a finite set of terms
that a specific proof actually needs, rather than asserted globally (which is
mathematically inconsistent for H2, H3, H4, and sha256 -- see notes above).
Meant to be passed as an explicit hypothesis on the theorems that need them.
-/

def CollisionResistantOn {α β: Type*} (H: α → β) (S: Set α): Prop :=
  Set.InjOn H S

def PreimageResistantOn {α β: Type*} (H: α → β) (known: Set α): Prop :=
  H ⁻¹' (H '' known) ⊆ known

-- open the namespaces defined by the class definition
open PoseidonHashes Sha
/-
Supply instances of PoseidonHashes and Sha

This makes sure we can just use H1, H2, sha256 etc.
https://lean-lang.org/doc/reference/4.26.0/Namespaces-and-Sections/#Lean___Parser___Command___variable
"Section variables are parameters that are automatically added to declarations that mention them."
-/
variable [PoseidonHashes] [Sha]

-- Keys, commitments, nullifiers
def pubKey (sk: F): F := H1 sk
def commit (amt pk r mint: F): F := H4 amt pk r mint
def signature (sk c: F) (leafIndex: Fin (2^26)): F := H3 sk c leafIndex
def nullifier (c sign: F) (leafIndex: Fin (2^26)): F := H3 c leafIndex sign

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

-- fixed for this circuit and thus relation S
variable (vk: Groth16.VerificationKey)

-- We assume: If a proof verifies, there is a witness
axiom soundnessRelationS: ∀ (π: Groth16.Proof) x, Groth16.verify vk π x → ∃ w, RelationS x w

end Groth16

-- Configurations for the privacy-cash contract
structure config where
  authority: Pubkey -- the authority that can change the config
  depositFeeRate: ℕ -- in basis points, e.g. 25 = 0.25%, default = 0
  withdrawalFeeRate: ℕ -- in basis points, default = 0.25%
  feeMarginError: ℕ -- in basis points, default = 500 (5% tolerance)
  -- NOTE: In solana code the max deposit limit in declared in the Merkle Tree but we have kept in here.
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

-- TODO do we need this? Depends on whether we want to include external balances
structure World where
  state: State
  balances: Pubkey → ℕ -- balances of (public) Solana accounts in lamports
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

/-
`transact` is written as follows:
- Preconditions are a Prop
- Effects are a function. Inputs: world, txInputs. Output: updated world.

`transact` is the combination of both: given oldWorld, newWorld and txInputs;
Preconditions are true AND newWorld equals effectsFunction on oldWorld and txInputs
-/
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

def externalDataHash (inputs: TxInputs): F :=
  let ext_data := serealizeExternalData inputs
  let hash := sha256 ext_data
  -- Convert the hash to F (ZMod p)
  let hashNat := hash.toNat
  (hashNat: F)

-- The actual moving of funds
def transferEffects (inputs: TxInputs) (oldWorld: World): World :=
  -- If the extAmt = 0, nothing changes. Otherwise return an updated version of the world.
  if inputs.extAmt = 0 then oldWorld else
    let extAmtAbs := Int.natAbs inputs.extAmt
    { oldWorld with
      state := {
        oldWorld.state with
        solBalance :=
          -- For a deposit, increase the solBalance in the state. For a withdrawal, lower it.
          -- TODO do we need a guard for underflow/overflow?
          if inputs.extAmt > 0 then oldWorld.state.solBalance + extAmtAbs
          else oldWorld.state.solBalance - extAmtAbs
      }
      balances :=  if inputs.extAmt > 0 then
        -- For a deposit, decrease the signer's SOL balance (in Solana account)
        -- TODO do we need a guard for underflow?
        Function.update oldWorld.balances inputs.s ((oldWorld.balances inputs.s) - extAmtAbs)
        else
        -- For a withdrawal, increase the SOL balance of the recipient (in Solana account)
        Function.update oldWorld.balances inputs.A ((oldWorld.balances inputs.A) + extAmtAbs)


    }

/-
- **Transfer**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#universal-joinsplit-transactions)):
    - (deposit) if $extAmt>0;$ SOL balance' = SOL balance $+ extAmt$ and $balances(s)' = balances(s) - extAmt$
    - (withdrawal) if $extAmt<0;$ SOL balance' = SOL balance $- |extAmt|$ and $balances(A)' = balances(A) + |extAmt|$
    - (transfer) if $extAmt=0;$ no changes to balances
-/
def transactEffects (inputs: TxInputs)(oldWorld: World): World :=
  -- Move the actual funds. In a separate function for clarity
  let worldAfterTransfers := transferEffects inputs oldWorld
  { worldAfterTransfers with
    state:= { worldAfterTransfers.state with
      -- Append outC0, then append outC1.
      -- This insert the output commitments & updates the Merkle root
      tree:= appendEffects inputs.outC1 (appendEffects inputs.outC0 oldWorld.state.tree)
      -- Add nullifiers to the state.
      nullifiers := oldWorld.state.nullifiers ∪ {inputs.k0, inputs.k1}
      -- The fee leaves the pool's SOL balance (paid out to the fee recipient below).
      solBalance := worldAfterTransfers.state.solBalance - inputs.f
    }
    -- Add the fee to the fee recipient's balance
    balances := Function.update oldWorld.balances inputs.t ((oldWorld.balances inputs.t) + inputs.f)
  }

structure transactPreconditions
  (vk: Groth16.VerificationKey)
  (inputs: TxInputs)
  (oldWorld: World): Prop where
  knownRoot: inputs.R ∈ Set.range oldWorld.state.tree.history
  externalDataBinding: externalDataHash inputs = inputs.extDataHash
  minimumFee:
    let feeErrorMargin := oldWorld.state.config.feeMarginError
    let feeRate := if inputs.extAmt > 0 then oldWorld.state.config.depositFeeRate else oldWorld.state.config.withdrawalFeeRate
    let expectedFee := (inputs.extAmt.natAbs * feeRate) / 10000
    let minAcceptableFee := (expectedFee * (10000 - feeErrorMargin)) / 10000
    inputs.f ≥ minAcceptableFee
  pubAmtConsistency:
    -- reference i64::MIN https://doc.rust-lang.org/std/i64/constant.MIN.html
    inputs.extAmt ≠ -9_223_372_036_854_775_808 ∧
    (inputs.extAmt > 0 → inputs.extAmt > inputs.f) ∧
    inputs.pubAmt = (inputs.extAmt: F) - inputs.f
  validZKP:
    let pubInputs: PubInputs := { R := inputs.R, pubAmt := inputs.pubAmt, extDataHash := inputs.extDataHash, nullifiers := ![inputs.k0, inputs.k1], outCommitments := ![inputs.outC0, inputs.outC1] }
    Groth16.verify vk inputs.π pubInputs
  newNullifiers: inputs.k0 ∉ oldWorld.state.nullifiers ∧ inputs.k1 ∉ oldWorld.state.nullifiers
  distinctNullifiers: inputs.k0 ≠ inputs.k1
  depositLimit:
    inputs.extAmt > 0 → inputs.extAmt ≤ oldWorld.state.config.maxDepositLimit
  poolSolvency:
    (inputs.extAmt < 0 → oldWorld.state.solBalance ≥ |inputs.extAmt| + inputs.f + oldWorld.rentExemptMin) ∧
    (inputs.extAmt ≥ 0 ∧ inputs.f > 0 → oldWorld.state.solBalance ≥ inputs.f +oldWorld.rentExemptMin)
  -- The 2 output commitments are added to the tree; make sure there is space for both
  treeNotFull: oldWorld.state.tree.nextIndex < (2^26-2)

-- ∧ is written by "\" + "and"
def transact
  (vk: Groth16.VerificationKey)
  (inputs: TxInputs)
  (oldWorld: World)
  (newWorld: World)
  : Prop :=
  -- Preconditions hold AND
  (transactPreconditions vk inputs oldWorld) ∧
  -- The effects have been executed correctly, i.e. the new world equals applying the effects function to the old world
    (transactEffects inputs oldWorld = newWorld)

--/////////////////////////////////////////
-- (5) Invariants
--/////////////////////////////////////////
