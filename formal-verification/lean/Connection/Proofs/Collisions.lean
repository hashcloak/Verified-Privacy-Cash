import Connection.Hypotheses
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Distinct addresses, inside the proofs (not for review)

The theorems do not assume collision resistance; they end in "… or an address collision occurs"
(`AddressCollision`). Inside the proofs, the
case without a collision gives: these seeds derive distinct addresses (`DistinctAddresses`). -/

namespace Connection

/-- `DistinctAddresses A S`: different seeds in `S` derive different addresses. -/
def DistinctAddresses (A : Addresses) (S : Set (List U8)) : Prop :=
  ∀ s₁ ∈ S, ∀ s₂ ∈ S, A.createProgramAddress s₁ = A.createProgramAddress s₂ → s₁ = s₂

/-- Without a collision among the seeds, their addresses are distinct. -/
theorem distinct_of_noCollision {A : Addresses} {S : Set (List U8)}
    (h : ¬ ∃ s₁ ∈ S, ∃ s₂ ∈ S, PdaCollision A s₁ s₂) : DistinctAddresses A S :=
  fun s₁ h₁ s₂ h₂ e => by
    by_contra hne
    exact h ⟨s₁, h₁, s₂, h₂, hne, e⟩

/-- Distinct addresses: no collision among the seeds. -/
theorem noCollision_of_distinct {A : Addresses} {S : Set (List U8)} (h : DistinctAddresses A S) :
    ¬ ∃ s₁ ∈ S, ∃ s₂ ∈ S, PdaCollision A s₁ s₂ :=
  fun ⟨s₁, h₁, s₂, h₂, hne, e⟩ => hne (h s₁ h₁ s₂ h₂ e)

/-- Distinctness is inherited by a subset of the seeds. -/
theorem DistinctAddresses.mono {A : Addresses} {s t : Set (List U8)} (h : DistinctAddresses A t)
    (hst : s ⊆ t) : DistinctAddresses A s :=
  fun x hx y hy e => h x (hst hx) y (hst hy) e

/-- Different seeds of a distinct set derive different addresses. -/
theorem ne_of_distinct {A : Addresses} {S : Set (List U8)} (h : DistinctAddresses A S)
    {s₁ s₂ : List U8} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) (hne : s₁ ≠ s₂) :
    A.createProgramAddress s₁ ≠ A.createProgramAddress s₂ :=
  fun e => hne (h s₁ h₁ s₂ h₂ e)

/-- The SOL tree, pool and config (with any bumps) are three different accounts, given distinct
    addresses for their seeds. -/
theorem singleton_pdas_distinct_of {A : Addresses} (b₁ b₂ b₃ : U8)
    (h : DistinctAddresses A {merkleTreeSeeds ++ [b₁], treeTokenSeeds ++ [b₂], globalConfigSeeds ++ [b₃]}) :
    A.createProgramAddress (merkleTreeSeeds ++ [b₁]) ≠ A.createProgramAddress (treeTokenSeeds ++ [b₂]) ∧
    A.createProgramAddress (merkleTreeSeeds ++ [b₁]) ≠ A.createProgramAddress (globalConfigSeeds ++ [b₃]) ∧
    A.createProgramAddress (treeTokenSeeds ++ [b₂]) ≠ A.createProgramAddress (globalConfigSeeds ++ [b₃]) := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := seed_lengths default default
  refine ⟨ne_of_distinct h (by simp) (by simp) (ne_of_length_ne ?_),
    ne_of_distinct h (by simp) (by simp) (ne_of_length_ne ?_),
    ne_of_distinct h (by simp) (by simp) (ne_of_length_ne ?_)⟩ <;> simp [h1, h3, h4]

/-- The two new nullifier accounts' seeds derive different addresses. -/
def NewNullifierAddressesDiffer (d : Deployment) (proof : zkcash_core.transact.Proof) : Prop :=
  DistinctAddresses d.toAddresses
    {d.pdaInput (nullifier0Seeds proof.input_nullifiers.val[0]!),
     d.pdaInput (nullifier1Seeds proof.input_nullifiers.val[1]!)}

/-- The transaction's seeds (`transactSeeds`) derive different addresses. -/
def TransactAddressesDistinct (d : Deployment) (proof : zkcash_core.transact.Proof) : Prop :=
  DistinctAddresses d.toAddresses (transactSeeds d proof)

/-- The fixed seeds are among a transaction's seeds. -/
theorem fixedSeeds_subset (d : Deployment) (proof : zkcash_core.transact.Proof) :
    fixedSeeds d ⊆ transactSeeds d proof :=
  Set.subset_union_left

/-- No collision for `proof`'s seeds: they derive distinct addresses. -/
theorem transactDistinct_of_noCollision {d : Deployment} {proofs : Set zkcash_core.transact.Proof}
    {proof : zkcash_core.transact.Proof} (hp : proof ∈ proofs) (h : ¬ AddressCollision d proofs) :
    TransactAddressesDistinct d proof :=
  distinct_of_noCollision fun hc => h (Or.inr ⟨proof, hp, hc⟩)

/-- No collision: the fixed seeds derive distinct addresses. -/
theorem fixedDistinct_of_noCollision {d : Deployment} {proofs : Set zkcash_core.transact.Proof}
    (h : ¬ AddressCollision d proofs) :
    DistinctAddresses d.toAddresses
      {d.pdaInput merkleTreeSeeds, d.pdaInput treeTokenSeeds, d.pdaInput globalConfigSeeds} :=
  distinct_of_noCollision fun hc => h (Or.inl hc)

/-- Distinct `transact` addresses: in particular the new nullifier accounts' differ. -/
theorem newDiffer_of_distinct {d : Deployment} {proof : zkcash_core.transact.Proof}
    (h : TransactAddressesDistinct d proof) : NewNullifierAddressesDiffer d proof :=
  DistinctAddresses.mono h (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    simp only [transactSeeds, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hx with rfl | rfl <;> simp)

theorem newDiffer_of_noCollision {d : Deployment} {proofs : Set zkcash_core.transact.Proof}
    {proof : zkcash_core.transact.Proof} (hp : proof ∈ proofs) (h : ¬ AddressCollision d proofs) :
    NewNullifierAddressesDiffer d proof :=
  newDiffer_of_distinct (transactDistinct_of_noCollision hp h)

/-- What one step of an execution needs, distinct addresses included. -/
def StepFacts (d : Deployment) (tx : TxEnv) : Instruction → Prop
  | .transact _ proof _ _ _ _ =>
    PdasDoNotSign d tx.toTxContext ∧ NewNullifierAddressesDiffer d proof ∧ CircuitFacts d {proof}
  | _ => True

/-- What an execution needs, distinct addresses included. -/
structure ExecutionFacts (d : Deployment) (evs : List Event) : Prop where
  fixedAddressesDiffer : DistinctAddresses d.toAddresses
    {d.pdaInput merkleTreeSeeds, d.pdaInput treeTokenSeeds, d.pdaInput globalConfigSeeds}
  eachStep : ∀ tx ix em, .program tx ix em ∈ evs → StepFacts d tx ix

/-- Without an address collision, the execution's assumptions give its facts. -/
theorem ExecutionFacts.of_assumptions {d : Deployment} {evs : List Event}
    (assume : ExecutionAssumptions d evs) (h : ¬ AddressCollision d (proofsIn evs)) :
    ExecutionFacts d evs where
  fixedAddressesDiffer := fixedDistinct_of_noCollision h
  eachStep := by
    intro tx ix em hm
    cases ix with
    | transact a proof ext fee out1 out2 =>
      have hin : TransactIn evs tx proof := ⟨a, ext, fee, out1, out2, em, hm⟩
      refine ⟨assume.pdasDoNotSign tx proof hin, newDiffer_of_noCollision (show proof ∈ proofsIn evs from ⟨tx, hin⟩) h, ?_⟩
      exact ⟨fun p hp => assume.circuit.distinctNullifiers p (by rw [hp]; exact ⟨tx, hin⟩)⟩
    | _ => trivial

/-- The facts give the assumptions (they only drop distinct addresses). -/
theorem ExecutionFacts.toAssumptions {d : Deployment} {evs : List Event}
    (h : ExecutionFacts d evs) : ExecutionAssumptions d evs where
  pdasDoNotSign := fun tx _ ⟨a, ext, fee, out1, out2, em, hm⟩ =>
    (h.eachStep tx (.transact a _ ext fee out1 out2) em hm).1
  circuit := ⟨fun p ⟨tx, a, ext, fee, out1, out2, em, hm⟩ =>
    (h.eachStep tx (.transact a p ext fee out1 out2) em hm).2.2.distinctNullifiers p rfl⟩

/-- No collision in an execution whose fixed seeds and transactions' seeds derive distinct
    addresses. -/
theorem noExecutionCollision {d : Deployment} {evs : List Event}
    (hf : DistinctAddresses d.toAddresses
      {d.pdaInput merkleTreeSeeds, d.pdaInput treeTokenSeeds, d.pdaInput globalConfigSeeds})
    (h : ∀ tx a proof ext fee out1 out2 em,
      Event.program tx (.transact a proof ext fee out1 out2) em ∈ evs →
      TransactAddressesDistinct d proof) :
    ¬ AddressCollision d (proofsIn evs) := by
  rintro (hc | ⟨proof, ⟨tx, a, ext, fee, out1, out2, em, hm⟩, hc⟩)
  · exact noCollision_of_distinct hf hc
  · exact noCollision_of_distinct (h _ _ _ _ _ _ _ _ hm) hc

/-- Distinct addresses: no address collision. -/
theorem noCollision_of_free {d : Deployment} {proof : zkcash_core.transact.Proof}
    (h : TransactAddressesDistinct d proof) : ¬ AddressCollision d {proof} := by
  rintro (hc | ⟨p, rfl, hc⟩)
  · exact noCollision_of_distinct (h.mono (fixedSeeds_subset d proof)) hc
  · exact noCollision_of_distinct h hc

/-- What the deployment's SHA-256 returns is the spec's `sha256` (from `HashesAgree`). -/
theorem HashesAgree.sha256_ok [Spec.PoseidonHashes] [Spec.Sha] {d : Deployment}
    (hashes : HashesAgree d) {x : Slice U8} {h : Std.Array U8 32#usize}
    (hh : d.crypto.sha256.hash x = ok h) : toBytes h.val = Spec.Sha.sha256 (toBytes x.val) :=
  hashes.sha256 x h hh

/-- A conclusion `P` that holds without an address collision holds, or a collision occurs. -/
theorem or_collision {P Q : Prop} (h : ¬ Q → P) : P ∨ Q := by
  by_cases hq : Q
  · exact Or.inr hq
  · exact Or.inl (h hq)

end Connection
