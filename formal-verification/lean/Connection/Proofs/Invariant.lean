import Connection.Mapping
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # The invariant `WellFormed`

`WellFormed`: facts about the program's own accounts (where they are, their shape, canonical
stored values) that hold in every state an execution reaches from genesis.

It is defined here and proved in `Proofs/WellFormed.lean` (`wf_reachable`). The connection
theorems do not assume it: their proofs derive it from the execution. Not for review. -/

namespace Connection

/-- `WellFormed d spent s` (invariant, proved): facts about the program's own accounts. They hold in every state
    an execution reaches from genesis, with `spent` the nullifiers that execution spent
    (proved in `Proofs/WellFormed.lean`). -/
structure WellFormed (d : Deployment) (spent : Finset LeanSpec.F) (s : State) : Prop where
  /-- The program is not the System Program (`DeploymentFacts.programNotSystem`, carried along
      so the invariant is self-contained). -/
  programNotSystem : d.programId ≠ systemProgram
  /-- Every Merkle tree the program owns is the SOL tree at its canonical address, with height
      26, a history of 100 roots and a current root index below 100. -/
  tree : ∀ k t, HoldsTree d.programId s k t → k = treeAddr d ∧ TreeShape t
  /-- Every pool account the program owns is the SOL pool at its canonical address. -/
  pool : ∀ k p, HoldsTreeToken d.programId s k p → k = poolAddr d
  /-- Every config the program owns is at its canonical address, and its deposit fee rate,
      withdrawal fee rate and fee error margin are each at most 10000 basis points (100%);
      `update_global_config` refuses larger values. -/
  config : ∀ k c, HoldsGlobalConfig d.programId s k c → k = configAddr d ∧
    c.deposit_fee_rate.val ≤ 10000 ∧ c.withdrawal_fee_rate.val ≤ 10000 ∧
    c.fee_error_margin.val ≤ 10000
  /-- Every nullifier the connection tracks as spent is the field value of some canonical
      32-byte nullifier whose nullifier account (slot 0 or slot 1) is owned by the program. -/
  spentRecorded : ∀ x ∈ spent, ∃ n : Pubkey, Canonical n ∧ toF n = x ∧
    ((s (d.pda (nullifier0Seeds n))).owner = d.programId ∨
      (s (d.pda (nullifier1Seeds n))).owner = d.programId)
  /-- Every root stored in the history of a tree the program owns is canonical (big-endian
      value below the field modulus): the program stores only the zero hashes, zero bytes and
      Poseidon outputs there (`HashesAgree.zeroBytesCanonical`, `poseidonCanonical`). -/
  storedRoots : ∀ k t, HoldsTree d.programId s k t → ∀ j : Fin 100, Canonical t.root_history.val[j.val]!
  /-- Every subtree stored in a tree the program owns is canonical: the program stores only
      zero hashes, leaves the verifier range-checked, and Poseidon outputs there. Needed by
      handler completeness (Poseidon answers only on canonical inputs). -/
  storedSubtrees : ∀ k t, HoldsTree d.programId s k t → ∀ j : Fin 26, Canonical t.subtrees.val[j.val]!

end Connection
