import Connection.ConnectionTheorems
import Connection.Proofs.ToySpend
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # A spec run that satisfies every hypothesis of run completeness (not for review)

The spec run of the example code run genesis, `initialize`, the deposit of 2 lamports
(`Proofs/ToyRun.lean`), obtained by soundness (`code_run_is_spec_run_pf`). It is a run of the
toy deployment (`RunOfDeployment`), its one transaction is neither L1 nor A0, and no address
collides. -/

namespace Connection.Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha toySpecGroups toySpecG1Group
  toySpecG1Module toySpecGTGroup toySpecPairing toySpecDeployment

/-- Bytes read back from a code array are that array. -/
theorem bytesToArray_toBytes {n : Usize} (a : Std.Array U8 n) : bytesToArray n (toBytes a.val) = a := by
  apply Std.Array.ext
  apply toBytes_inj
  rw [toBytes_bytesToArray (by simp [toBytes])]

/-- The deposit, as the spec sees it. -/
abbrev depInputs : Spec.TxInputs := toInputs ⟨⟨toyTx.signers⟩, depA, ⟨depProof, 2#i64, 0#u64, emptySlice, emptySlice⟩⟩

/-- The deposit's addresses, as the code transaction built from the spec's inputs, are distinct. -/
theorem depInputs_distinct : TransactAddressesDistinct toyD (fromSpecProof depInputs) := by
  have h0 : (fromSpecProof depInputs).input_nullifiers.val[0]! = depProof.input_nullifiers.val[0]! := by
    show bytesToArray 32#usize (toBytes depProof.input_nullifiers.val[0]!.val) = _
    exact bytesToArray_toBytes _
  have h1 : (fromSpecProof depInputs).input_nullifiers.val[1]! = depProof.input_nullifiers.val[1]! := by
    show bytesToArray 32#usize (toBytes depProof.input_nullifiers.val[1]!.val) = _
    exact bytesToArray_toBytes _
  unfold TransactAddressesDistinct transactSeeds
  rw [h0, h1]
  exact toy_collisionFree_dep

/-- **Every hypothesis of `run_complete_except_L1_A0` holds for a spec run with a transaction.** -/
theorem toy_run_complete_nonvacuous (h64 : Usize.max = 2 ^ 64 - 1) :
    ∃ (params : Spec.InitParams) (r : SpecRun toyC params),
      ProgramNotSystem toyD ∧ PairingLaws toyC.e ∧ HashesAgree toyD
      ∧ CryptoSucceeds toyD.crypto toyC ∧ RuntimeFacts toyRent
      ∧ RunOfDeployment toyD toyRent params
      ∧ (∀ tx ∈ r.txs, tx.extAmt ≠ 0)
      ∧ (∀ tx ∈ r.txs, tx.π.A ≠ List.replicate 64 0)
      ∧ ¬ AddressCollision toyD (fromSpecProof '' {tx | tx ∈ r.txs})
      ∧ r.txs = [depInputs] := by
  obtain ⟨s₁, s₂, e₂, h1, -, hpid, h2, -, depAssumptions, depAddressesDiffer, -⟩ := toy_run
  have hpath : CodeRun toyD toyS0 [⟨toyS0, .program toyTx (.initialize toyInitA) [], s₁⟩,
      ⟨s₁, .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂, s₂⟩] s₂ :=
    .program h1 toyTx_rentPositive (.program h2 toyTx_rentPositive (.nil _))
  have runFacts : RunFacts toyD [.program toyTx (.initialize toyInitA) [],
      .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂] := by
    refine ⟨toy_fixed_addresses, ?_⟩
    intro tx ix em hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h <;> cases h
    · trivial
    · exact ⟨depAssumptions, depAddressesDiffer⟩
  have sameRent : ∀ tx ix em, Event.program tx ix em ∈ [.program toyTx (.initialize toyInitA) [],
      .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂] →
      SameRent toyRent tx.minimumBalance := by
    intro tx ix em hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h <;> cases h <;> rfl
  rcases code_run_is_spec_run_pf toyGenesis hpath hpid toyC toyLaws toyHashesAgree runFacts sameRent with
    ⟨-, htx⟩ | ⟨params, r, hrun'⟩
  · simp [eventsOf, runTxs, stepTxs] at htx
  have hdep := hrun'.deployment
  have htx := hrun'.txs
  have hr : r.txs = [depInputs] := by rw [htx]; rfl
  have hj : ∀ tx ∈ r.txs, tx = depInputs := by
    intro tx h
    rw [hr] at h
    exact List.mem_singleton.mp h
  refine ⟨params, r, toyProgramNotSystem, toyLaws, toyHashesAgree, toyCryptoSucceeds, toyRuntime h64,
    hdep, ?_, ?_, ?_, hr⟩
  · intro tx h
    rw [hj tx h]
    simp [toInputs]
  · intro tx h
    rw [hj tx h]
    intro e
    apply alpha_ne_zeros
    apply toBytes_inj
    exact e.trans (by simp [toBytes])
  · rintro (hf | ⟨_, ⟨tx, h, rfl⟩, hc⟩)
    · exact noCollision_of_distinct toy_fixed_addresses hf
    · rw [hj tx h] at hc
      exact noCollision_of_distinct depInputs_distinct hc

end Connection.Toy
