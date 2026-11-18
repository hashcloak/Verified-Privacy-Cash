import Connection.Proofs.Basic
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # The invariant `WellFormed`

`WellFormed`: facts about the program's own accounts (where they are, their shape, canonical
stored values) that hold in every state an execution reaches from genesis.

It is defined here and proved in `Proofs/WellFormed.lean` (`wf_reachable`). The connection
theorems do not assume it: their proofs derive it from the execution. Not for review. -/

namespace Connection

/-- `WellFormed d s` (invariant, proved): facts about the program's own accounts. They hold in
    every state an execution reaches from genesis (proved in `Proofs/WellFormed.lean`). -/
structure WellFormed (d : Deployment) (s : State) : Prop where
  /-- The program is not the System Program (`ProgramNotSystem`, carried along
      so the invariant is self-contained). -/
  programNotSystem : d.programId ≠ systemProgram
  /-- Every Merkle tree the program owns is the SOL tree at its canonical address, with height
      26, a history of 100 roots and a current root index below 100, and it stores the canonical
      bump of its address (`initialize` writes it, no instruction changes it). -/
  tree : ∀ k t, HoldsTree d.programId s k t → k = d.treeAddress ∧ TreeShape t ∧
    t.bump = d.canonicalBump merkleTreeSeeds
  /-- Every pool account the program owns is the SOL pool at its canonical address, and it stores
      the canonical bump of its address. -/
  pool : ∀ k p, HoldsTreeToken d.programId s k p → k = d.poolAddress ∧
    p.bump = d.canonicalBump treeTokenSeeds
  /-- Every config the program owns is at its canonical address, and its deposit fee rate,
      withdrawal fee rate and fee error margin are each at most 10000 basis points (100%);
      `update_global_config` refuses larger values. It stores the canonical bump of its address. -/
  config : ∀ k c, HoldsGlobalConfig d.programId s k c → k = d.configAddress ∧
    c.deposit_fee_rate.val ≤ 10000 ∧ c.withdrawal_fee_rate.val ≤ 10000 ∧
    c.fee_error_margin.val ≤ 10000 ∧ c.bump = d.canonicalBump globalConfigSeeds
  /-- Every root stored in the history of a tree the program owns is canonical (big-endian
      value below the field modulus): the program stores only the zero hashes, zero bytes and
      Poseidon outputs of canonical values there (`HashesAgree.zeroBytes`, `HashesAgree.poseidon`). -/
  storedRoots : ∀ k t, HoldsTree d.programId s k t → ∀ j : Fin 100, Canonical t.root_history.val[j.val]!
  /-- Every subtree stored in a tree the program owns is canonical: the program stores only
      zero hashes, leaves the verifier range-checked, and Poseidon outputs there. Needed by
      completeness (Poseidon answers only on canonical inputs). -/
  storedSubtrees : ∀ k t, HoldsTree d.programId s k t → ∀ j : Fin 26, Canonical t.subtrees.val[j.val]!
  /-- Every nullifier account the program owns is at an address derived for the program: only
      `transact` creates nullifier accounts, and Anchor checks their addresses. -/
  nullifiers : ∀ k b, (s k).owner = d.programId ∧ (s k).data = .nullifier b → ∃ seeds, k = d.pda seeds

end Connection
