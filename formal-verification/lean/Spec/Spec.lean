import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Fin

--///////// Note: SOL ONLY. In Phase 2 we'll distinguish between SOL and SPL.

-- Everything below lives in `LeanSpec`, not the root namespace: several names here
-- (`Tree`, `Byte`, ...) are generic enough to collide with Mathlib/Aeneas root-level
-- declarations once a file imports both this spec and the code model (exactly what the
-- connection does). The connection refers to spec names as `LeanSpec.name`.
namespace LeanSpec

--/////////////////////////////////////////
-- Definitions
--/////////////////////////////////////////
def p: ℕ := 21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- `[NeZero p]` for the field-to-`ℤ` lifting lemmas used by G1c (`p` is a `def`, so the
    instance is not found automatically). -/
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

/-- Read bytes as a number, big-endian (byte 0 is most significant), as the program's
    Groth16 verifier reads its public inputs. -/
def natOfBE (bs : Bytes) : ℕ := bs.foldl (fun acc b => 256 * acc + b.toNat) 0

/-- `bs` is the canonical encoding of the field element `x`, as the sender sends a public
    input: 32 bytes whose big-endian value is below `p` and is `x`. Every field element has
    exactly one canonical encoding; a non-canonical one (value `x + p`, …) is rejected. -/
def canonicalEncoding (bs : Bytes) (x : F) : Prop :=
  bs.length = 32 ∧ natOfBE bs < p ∧ (natOfBE bs : F) = x

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
  collision : H1 a = H1 b

/-- A note: what a commitment commits to. -/
structure Note where
  amount : F
  ownerPk : F   -- the owner's public key, `H1` of the owner's secret key
  blinding : F
  mint : F

/-- Two different notes with the same `H4` output (so the same commitment). -/
structure H4Collision (a b : Note) : Prop where
  ne : a ≠ b
  collision : H4 a.amount a.ownerPk a.blinding a.mint = H4 b.amount b.ownerPk b.blinding b.mint

/-- Two different argument pairs with the same `H2` output -- the binary Merkle hash used
    in `Opening.calcRoot` and `appendEffects`. Used by G1a (`PathCollision`). -/
structure H2Collision (a b : F × F) : Prop where
  ne : a ≠ b
  collision : H2 a.1 a.2 = H2 b.1 b.2

/-- Two different argument triples with the same `H3` output (`H3` builds nullifiers and
    signatures). Needed by G2b. -/
structure H3Collision (a b : F × F × F) : Prop where
  ne : a ≠ b
  collision : H3 a.1 a.2.1 a.2.2 = H3 b.1 b.2.1 b.2.2

/-- Two different byte strings whose little-endian, mod-`p` reduced `sha256` digests
    collide -- the actual hash used to bind external transaction data
    (`externalDataHash`) into the circuit's public inputs. A weaker (hence easier to
    obtain) break than a raw `sha256` collision, since it also holds when two distinct
    digests happen to agree mod `p`. -/
structure Sha256Collision (a b : Bytes) : Prop where
  ne : a ≠ b
  collision : (natOfLE (sha256 a) : F) = (natOfLE (sha256 b) : F)

/-- An `H4` preimage of `0`. An unwritten leaf holds `Z 0 = 0`, so a spend that opens an
    unwritten leaf with a real note needs a note that commits to `0`. Used by G1a. -/
structure H4ZeroPreimage (a : Note) : Prop where
  preimage : H4 a.amount a.ownerPk a.blinding a.mint = 0

/-- An `H2` preimage of `0`: a pair that `H2` hashes to `0`. A Merkle root equal to `0`
    (which `rootKnown` rejects) needs one. Used by G3a. -/
structure H2ZeroPreimage (a : F × F) : Prop where
  preimage : H2 a.1 a.2 = 0

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
  : (⟨amt, pk, r, mint⟩ : Note) = ⟨amt', pk', r', mint'⟩
    ∨ H4Collision ⟨amt, pk, r, mint⟩ ⟨amt', pk', r', mint'⟩ := by
  by_cases heq : (⟨amt, pk, r, mint⟩ : Note) = ⟨amt', pk', r', mint'⟩
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
  -- Inputs are not range-checked: G1a shows a spent amount equals the amount of the note
  -- it opens, which was range-checked when that note was created as an output.
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
/-- The three groups of the pairing, and how a sender's bytes are read as points of `G1` and
    `G2` (`none`: the bytes are not a point). A class rather than fixed `opaque` types, so
    that a deployment (and the code connection) can instantiate them with the real BN254
    groups and the syscalls' decoding. The spec says nothing about the encoding itself. -/
class Groups where
  G1 : Type
  G2 : Type
  GT : Type
  decodeG1 : Bytes → Option G1
  decodeG2 : Bytes → Option G2
variable [Groups]
abbrev G1 : Type := Groups.G1
abbrev G2 : Type := Groups.G2
abbrev GT : Type := Groups.GT
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

/-- A proof as the sender sends it: the bytes of its three points. -/
structure ProofBytes where
  A: Bytes
  B: Bytes
  C: Bytes

/-- The proof's three points, decoded (`Groups.decodeG1`, `Groups.decodeG2`); `none` if one
    of them is not a point. -/
def ProofBytes.decode (πb: ProofBytes) : Option Proof :=
  match Groups.decodeG1 πb.A, Groups.decodeG2 πb.B, Groups.decodeG1 πb.C with
  | some A, some B, some C => some ⟨A, B, C⟩
  | _, _, _ => none

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

end Groth16

class Deployment where
  vk: Groth16.VerificationKey -- the deployed verification key (a fixed circuit)

variable [Deployment]

-- No soundness axiom. Perfect soundness ("a verifying proof implies a witness exists") is
-- false for Groth16: for any statement a verifying proof exists mathematically, it is only
-- infeasible to find. So the theorems take the witnesses as data instead (`wit`, read as
-- the knowledge extractor's output; trusted assumption T1 in `Spec/Statements.lean`).

/-- Groth16 completeness for the deployed key: every statement with a witness has a proof,
    sent as bytes, whose points decode and which verifies. True for an honestly generated key
    (Groth16 has perfect completeness; the prover writes the points it computes in the
    format the decoders read). A hypothesis of G3a only. -/
def Groth16Complete : Prop :=
  ∀ x w, RelationS x w → ∃ πb : Groth16.ProofBytes, ∃ π,
    πb.decode = some π ∧ Groth16.verify Deployment.vk π x

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
  pool: Pubkey -- the pool's account (the `tree_token` PDA), which holds the pool's SOL
  config: config

-- Needed: `balances` is how deposits/withdrawals/fees actually move real SOL between
-- accounts (`transferEffects`, `transactEffects`), how `AgreesOnProgramEffects`
-- states who is paid, and how `signerSolvent` checks a
-- depositor can cover their deposit. Without it there'd be nothing to state those over.
structure World where
  state: State
  balances: Pubkey → ℕ -- balances of (public) Solana accounts in lamports
  -- the minimum lamport balance an account must have to keep existing without paying rent
  rentExemptMin: ℕ
  -- the lamports the signer pays (the rent-exempt minimum) for each nullifier account a
  -- transaction creates
  nullifierRent: ℕ

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
  π: Groth16.ProofBytes -- Groth16 proof for relation S, as the sender's bytes
  mintAddr: Pubkey -- token type
  -- The seven public inputs as the sender sends them, 32 bytes each, in circuit order
  -- (`Groth16.toVector`: root, public amount, external data hash, the two nullifiers, the
  -- two output commitments). `publicInputsEncoded` ties them to the field elements above.
  pubInputBytes: Fin 7 → Bytes

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

/-- The pool's SOL: the balance of the pool's account. -/
def World.poolBalance (w : World) : ℕ := w.balances w.state.pool

/-- Move `x` lamports from account `src` to account `dst`. -/
def moveLamports (b : Pubkey → ℕ) (src dst : Pubkey) (x : ℕ) : Pubkey → ℕ :=
  let b' := Function.update b src (b src - x)
  Function.update b' dst (b' dst + x)

/- The actual moving of funds (note that this does not pay fees)
  **Transfer**([doc ref](https://privacy-cash-privacy-cash.mintlify.app/concepts/how-it-works#universal-joinsplit-transactions)):
    - (deposit) if $extAmt>0$: move $extAmt$ from the signer $s$ to the pool
    - (withdrawal) if $extAmt<0$: move $|extAmt|$ from the pool to the recipient $A$
    - (transfer) if $extAmt=0$: no changes to external balances

  No ℕ underflow: `signerSolvency` and `poolSolvency` rule it out.
-/
def transferEffects (inputs: TxInputs) (oldWorld: World): World :=
  if inputs.extAmt = 0 then oldWorld else
    let extAmtAbs := Int.natAbs inputs.extAmt
    { oldWorld with
      balances := if inputs.extAmt > 0
        then moveLamports oldWorld.balances inputs.s oldWorld.state.pool extAmtAbs
        else moveLamports oldWorld.balances oldWorld.state.pool inputs.A extAmtAbs }

-- The signer pays the rent for the two nullifier accounts a transaction creates (Anchor
-- `init` with `payer = signer` on `nullifier0` and `nullifier1`, before the instruction body
-- runs). Network fees are charged by the runtime before the program runs, so they are not
-- part of the balances the program sees.
def nullifierRentEffects (inputs: TxInputs) (oldWorld: World): World :=
  let rentPaid := oldWorld.balances inputs.s - 2 * oldWorld.nullifierRent
  { oldWorld with balances := Function.update oldWorld.balances inputs.s rentPaid }

-- Returns a new World after updating all necessary elements according to the txInputs
def transactEffects (inputs: TxInputs)(oldWorld: World): World :=
  -- Pay the nullifier rent, then move the actual funds. In separate functions for clarity
  let worldAfterTransfers := transferEffects inputs (nullifierRentEffects inputs oldWorld)
  { worldAfterTransfers with
    state:= { worldAfterTransfers.state with
      -- Append outC0, then append outC1.
      -- This insert the output commitments & updates the Merkle root
      tree:= appendEffects inputs.outC1 (appendEffects inputs.outC0 worldAfterTransfers.state.tree)
      -- Add nullifiers to the state.
      nullifiers := worldAfterTransfers.state.nullifiers ∪ {inputs.k0, inputs.k1}
    }
    -- The fee moves from the pool to the fee recipient
    balances := moveLamports worldAfterTransfers.balances worldAfterTransfers.state.pool inputs.t
      inputs.f
  }

/-- What one transaction moves into (positive) or out of (negative) account `k`, summed
    over every role `k` plays: the recipient receives `|extAmt|` on a withdrawal, the fee
    recipient receives `f`, the signer pays `extAmt` on a deposit and the rent for the two
    nullifier accounts (`rent` each), and the pool gains `extAmt − f`. An account with
    several roles (e.g. a relayer that signs and collects the fee) gets the sum. -/
def balanceDelta (inputs : TxInputs) (pool : Pubkey) (rent : ℕ) (k : Pubkey) : ℤ :=
  (if k = inputs.A ∧ inputs.extAmt < 0 then (inputs.extAmt.natAbs : ℤ) else 0)
  + (if k = inputs.t then (inputs.f : ℤ) else 0)
  - (if k = inputs.s ∧ inputs.extAmt > 0 then inputs.extAmt else 0)
  - (if k = inputs.s then 2 * (rent : ℤ) else 0)
  + (if k = pool then inputs.extAmt - inputs.f else 0)

--/////////////////////////////////////////
-- Preconditions, one named condition each.
-- Each is stated over the plain values it depends on, so the code-side theorem for
-- the corresponding Rust check can refer to it directly.
--/////////////////////////////////////////

-- R is a non-zero root in the tree's root history.
def rootKnown (T: Tree) (R: F): Prop :=
  R ∈ Set.range T.history ∧ R ≠ 0

-- `rootKnown`, for the root as the sender sends it: 32 bytes, canonical (big-endian value
-- below `p`), whose value is a known root. The program compares the bytes with the stored
-- roots' bytes.
def rootBytesKnown (T: Tree) (bs: Bytes): Prop :=
  bs.length = 32 ∧ natOfBE bs < p ∧ rootKnown T (natOfBE bs : F)

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
-- A deposit must exceed its fee. A transfer (extAmt = 0) is allowed; its fee is paid
-- from the pool (see `transferEffects`).
def pubAmtConsistent (extAmt: ℤ) (f: ℕ) (pubAmt: F): Prop :=
  (extAmt > 0 → extAmt > f) ∧
  pubAmt = (extAmt: F) - f

-- The Groth16 proof is valid for the deployed key and these public inputs. Two checks:
-- the proof's bytes decode to points (`Groups.decodeG1`, `decodeG2`; the wire format, NOT
-- FROM THE DOCS), and the decoded points satisfy the Groth16 equation. Bytes that are not
-- points are no proof at all, so decoding is part of validity, not a separate check.
def proofValid (inputs: TxInputs): Prop :=
  ∃ π, inputs.π.decode = some π ∧ Groth16.verify Deployment.vk π inputs.pubInputs

-- Each of the seven public inputs is sent as its canonical encoding: 32 bytes whose
-- big-endian value is below `p` and is the field element the spec uses.
-- NOT FROM THE DOCS: it is the wire format. Guards against input aliasing: without it the
-- bytes of `x + p` would be accepted as `x`, so one nullifier could be sent as two different
-- byte strings (two different nullifier accounts on-chain) while the spec sees one.
def publicInputsEncoded (inputs: TxInputs): Prop :=
  ∀ i, canonicalEncoding (inputs.pubInputBytes i) (Groth16.toVector inputs.pubInputs i)

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

-- The pool can pay out the withdrawal and the fee and still keep its rent reserve. On a
-- deposit the fee is paid after the deposit has arrived (`transactEffects` moves the deposit
-- first), so the deposit counts.
def poolSolvent (poolBalance rentExemptMin: ℕ) (extAmt: ℤ) (f: ℕ): Prop :=
  (extAmt < 0 → poolBalance ≥ |extAmt| + f + rentExemptMin) ∧
  (extAmt ≥ 0 ∧ f > 0 → poolBalance + extAmt ≥ f + rentExemptMin)

-- The signer can pay the rent for the two nullifier accounts and, on a deposit, the deposit.
-- Enforced on-chain: Anchor's `init` fails if the signer can't pay the rent, and the deposit
-- transfer fails if the signer can't cover it. It isn't a silent underflow.
def signerSolvent (balances: Pubkey → ℕ) (s: Pubkey) (extAmt: ℤ) (nullifierRent: ℕ): Prop :=
  balances s ≥ 2 * nullifierRent + (if extAmt > 0 then extAmt.natAbs else 0)

-- There is room in the tree for the two output commitments (the tree holds `2^26` leaves).
def treeHasRoom (T: Tree): Prop :=
  T.nextIndex ≤ 2^26 - 2

-- `extAmt` fits an i64 and the fee a u64, as in the code (`ext_amount: i64`, `fee: u64`).
-- Without it the spec allows e.g. `extAmt = −p`: the proof sees `pubAmt = −f` (mod `p`),
-- yet `p` lamports are withdrawn.
-- NOT FROM THE DOCS: `extAmt = −2^63` (`i64::MIN`) is excluded. A withdrawal's amount is
-- `−extAmt`, which does not fit an i64 there; the code rejects it. The docs should say so.
-- No real withdrawal is affected: `2^63` lamports exceeds the total SOL supply.
def amountsInRange (extAmt: ℤ) (f: ℕ): Prop :=
  -2^63 < extAmt ∧ extAmt < 2^63 ∧ f < 2^64

-- Each encrypted output is shorter than `2^32` bytes. Borsh writes a vector's length as a
-- `u32` and fails on longer vectors (`u32::try_from`); Solana's transaction size limit
-- (1232 bytes) keeps them far below that anyway.
def encOutsFit (inputs: TxInputs): Prop :=
  inputs.encOut0.length < 2^32 ∧ inputs.encOut1.length < 2^32

-- The pool's account is not the signer, and is not paid as recipient or fee recipient.
-- NOT FROM THE DOCS: a modelling precondition. It makes the pool's balance change by exactly
-- `extAmt − f` (`sol_balance_correctness_step`), which G1c (every unspent note is backed by SOL
-- in the pool) and G4a (no SOL is created or lost) rely on: a withdrawal paid to the pool
-- would spend notes while the SOL stays in the pool. It holds on Solana: the signer can't be
-- the pool (a program address can't sign); if the pool is paid as recipient or fee recipient,
-- the program reads both balances and then writes both, which would create lamports, and the
-- runtime rejects any instruction that doesn't conserve lamports (the program itself doesn't
-- check this). Naming the pool where it is not paid (the recipient of a deposit, the fee
-- recipient of a zero fee) is allowed: nothing moves.
def poolIsSeparate (inputs: TxInputs) (pool: Pubkey): Prop :=
  inputs.s ≠ pool ∧ (inputs.extAmt < 0 → inputs.A ≠ pool) ∧ (inputs.f > 0 → inputs.t ≠ pool)

-- Every balance a payment credits is below 2^64 after that payment: every account the
-- transaction credits (`balanceDelta` positive) ends below 2^64, and so does the pool right
-- after a deposit, before the fee is paid from it (`transactEffects` moves the deposit
-- first). Solana balances are `u64`; a payment that would overflow is rejected.
-- NOT FROM THE DOCS. No real transaction is affected: 2^64 lamports exceeds the total SOL
-- supply. The pool between deposit and fee is the only intermediate balance that can exceed
-- a final one (every other payment only adds to its payee's final balance).
def balancesFit (inputs: TxInputs) (w: World): Prop :=
  (∀ k, 0 < balanceDelta inputs w.state.pool w.nullifierRent k →
    (w.balances k : ℤ) + balanceDelta inputs w.state.pool w.nullifierRent k < 2^64) ∧
  (inputs.extAmt > 0 → (w.poolBalance : ℤ) + inputs.extAmt < 2^64)

structure transactPreconditions
  (inputs: TxInputs)
  (oldWorld: World): Prop where
  knownRoot: rootBytesKnown oldWorld.state.tree (inputs.pubInputBytes 0)
  externalDataBinding: externalDataBound inputs
  minimumFee: feeSufficient oldWorld.state.config inputs.extAmt inputs.f
  pubAmtConsistency: pubAmtConsistent inputs.extAmt inputs.f inputs.pubAmt
  validZKP: proofValid inputs
  newNullifiers: nullifiersFresh oldWorld.state.nullifiers inputs.k0 inputs.k1
  distinctNullifiers: nullifiersDistinct inputs.k0 inputs.k1
  depositLimit: depositWithinLimit oldWorld.state.config inputs.extAmt
  poolSolvency: poolSolvent oldWorld.poolBalance oldWorld.rentExemptMin inputs.extAmt inputs.f
  signerSolvency: signerSolvent oldWorld.balances inputs.s inputs.extAmt oldWorld.nullifierRent
  -- The 2 output commitments are added to the tree; make sure there is space for both
  treeNotFull: treeHasRoom oldWorld.state.tree
  amountRange: amountsInRange inputs.extAmt inputs.f
  encOutLength: encOutsFit inputs
  poolSeparate: poolIsSeparate inputs oldWorld.state.pool
  canonicalInputs: publicInputsEncoded inputs
  balancesFit: balancesFit inputs oldWorld

/-- `actual` agrees with `predicted` on everything, field by field: every account balance
    (uninvolved accounts stay unchanged, the pool's included), the pool's address, the tree, the nullifiers, the config and
    the rent amounts. Kept field by field so the code-side theorem can prove each part on
    its own. -/
structure AgreesOnProgramEffects (inputs : TxInputs) (predicted actual : World) : Prop where
  tree          : actual.state.tree = predicted.state.tree
  nullifiers    : actual.state.nullifiers = predicted.state.nullifiers
  pool          : actual.state.pool = predicted.state.pool
  config        : actual.state.config = predicted.state.config
  rentExemptMin : actual.rentExemptMin = predicted.rentExemptMin
  nullifierRent : actual.nullifierRent = predicted.nullifierRent
  balances      : actual.balances = predicted.balances

/-
`transact` holds when a transaction from `oldWorld` to `newWorld` is allowed and has
the effects the program is responsible for: the preconditions hold in `oldWorld`, and
`newWorld` agrees with `transactEffects inputs oldWorld` per `AgreesOnProgramEffects`
(see its doc comment for why this isn't exact equality).
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

-- The initial state and reachability (used in the statements).

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
-- it). Its balance counts the pool's total lamports, rent reserve included -- the same
-- reading `poolSolvent` uses (`poolBalance ≥ … + rentExemptMin`).
/-- The parameters of a freshly initialized pool. -/
structure InitParams where
  cfg : config
  balances : Pubkey → ℕ  -- every account's balance (the pool's is overwritten below)
  rentExemptMin : ℕ
  nullifierRent : ℕ
  pool : Pubkey          -- the pool's account

def initWorld (params : InitParams) : World := {
  state := {
    tree := initTree
    nullifiers := ∅
    pool := params.pool
    config := params.cfg
  }
  balances := Function.update params.balances params.pool params.rentExemptMin
  rentExemptMin := params.rentExemptMin
  nullifierRent := params.nullifierRent
}

/-- A donation: `x` lamports credited to the pool's account, nothing else changes. On Solana
    anyone can send SOL to any account at any time, the pool's included, also before
    `initialize` (Anchor's `init` then only tops the account up to the rent-exempt minimum).
    The program cannot prevent it and does not see it as a transaction. Other accounts are
    not modelled: no theorem compares their balances across transactions. -/
def World.donate (w: World) (x: ℕ) : World :=
  { w with balances := Function.update w.balances w.state.pool (w.balances w.state.pool + x) }

-- A claim about a pair of worlds; can we go from w1 to w2?
--   This lets us reason about "in any number of steps"
inductive ReachableWorld: World → World → Prop where
  -- No transactions; true for any world
 | noStep(w1: World): ReachableWorld w1 w1
 -- Given a reachable pair w1, w2, a donation `d` to the pool, and
 -- a proof that transact succeeds from w2 (with the donation credited) to w3,
 -- Then obtain proof that w3 is reachable from w1
 | extend{w1 w2 w3: World}(d: ℕ)(txInputs: TxInputs):
      ReachableWorld w1 w2 →
      transact txInputs (w2.donate d) w3 →
       ReachableWorld w1 w3

end LeanSpec
