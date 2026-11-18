import Connection.Mapping
open Aeneas Aeneas.Std Result

/-! # Breaks: address collisions

REVIEW SURFACE. A program-derived address is `SHA-256(seeds ‖ bump ‖ programId ‖
"ProgramDerivedAddress")`, with the canonical bump of `find_program_address` (core-model's
`pdaInput`). As in the spec (T2, `NullifierAddressCollision`), collision resistance is not
assumed: a theorem that needs two derived addresses to differ ends in "… or an address collision
occurs", two named seeds deriving the same address (core-model's `PdaCollision`). Different
seeds give different hash inputs, so this is a SHA-256 collision.
-/

namespace Connection

/-- `fixedSeeds d`: the seeds, with bumps, of the tree, the pool and the config. -/
def fixedSeeds (d : CodeModel.Deployment) : Set (List U8) :=
  {d.pdaInput CodeModel.merkleTreeSeeds, d.pdaInput CodeModel.treeTokenSeeds,
   d.pdaInput CodeModel.globalConfigSeeds}

/-- `transactSeeds d proof`: the seeds, with bumps, of the addresses a `transact` with this proof
    uses: the tree, the pool, the config (`fixedSeeds`, included so that a nullifier address
    colliding with one of them counts), and both slots of both input nullifiers. The code
    creates `nullifier0` of the first and `nullifier1` of the second, and requires the crossed
    slots to be free system accounts. -/
def transactSeeds (d : CodeModel.Deployment) (proof : CodeModel.Proof) : Set (List U8) :=
  fixedSeeds d ∪
    {d.pdaInput (CodeModel.nullifier0Seeds proof.input_nullifiers.val[0]!),
     d.pdaInput (CodeModel.nullifier1Seeds proof.input_nullifiers.val[1]!),
     d.pdaInput (CodeModel.nullifier0Seeds proof.input_nullifiers.val[1]!),
     d.pdaInput (CodeModel.nullifier1Seeds proof.input_nullifiers.val[0]!)}

/-- `SeedCollision d S`: two different seeds in `S` derive the same address. -/
def SeedCollision (d : CodeModel.Deployment) (S : Set (List U8)) : Prop :=
  -- under the deployment's address derivation (`d.toAddresses`: its program id and bumps)
  ∃ s₁ ∈ S, ∃ s₂ ∈ S, CodeModel.PdaCollision d.toAddresses s₁ s₂

/-- `AddressCollision d proofs` (a break): two program-derived addresses collide, where the two are
    - two of the tree, the pool and the config (`fixedSeeds`), or
    - a nullifier address of one `transact` with a proof in `proofs` and the tree, the pool or the
      config, or
    - two nullifier addresses of the same such `transact` (both slots of both input nullifiers;
      `transactSeeds`).

    Addresses of different transactions are not compared: the spec already rejects a new
    nullifier account at an existing address (`nullifierAccountsCreatable`, as Anchor's `init`
    does).

    For one transaction, `proofs` is `{proof}`; for an execution, its proofs (`proofsIn`); for a
    spec run, its transactions' proofs read as the code's (`fromSpecProof`). -/
def AddressCollision (d : CodeModel.Deployment) (proofs : Set CodeModel.Proof) : Prop :=
  SeedCollision d (fixedSeeds d) ∨ ∃ proof ∈ proofs, SeedCollision d (transactSeeds d proof)

end Connection
