import Connection.Proofs.ToySpend
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # A toy execution with an admin change inside the run (not for review)

Genesis, `initialize`, `update_deposit_limit` (the authority sets the limit to 7 lamports), then
the deposit of 2 lamports of `Connection/Proofs/ToyRun.lean`. Because a transaction follows the
admin instruction, the change is in the spec run (`IsRunOf`): every spec run of the execution
records it. So G5a and G5b for the code are not vacuous on an admin change
(`toy_admin_change_nonvacuous`). -/

namespace Connection.Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha toySpecGroups toySpecG1Group
  toySpecG1Module toySpecGTGroup toySpecPairing toySpecDeployment

/-- **The authority can change the deposit limit**: after the toy `initialize`,
    `update_deposit_limit` to 7 lamports, signed by the authority, is accepted, and only the tree's
    limit changes. -/
theorem toy_admin_step {s₁ : State} {tree : merkle_tree.MerkleTreeAccount}
    (hT : s₁ treeA = ⟨1#u64, toyD.programId, .treeAccount tree⟩) (hTb : tree.bump = 255#u8)
    (hauth : tree.authority = pk 1#u8) :
    step toyD s₁ toyTx (.updateDepositLimit ⟨treeA, pk 1#u8⟩ 7#u64) =
      .ok (s₁.set treeA ⟨1#u64, toyD.programId, .treeAccount { tree with max_deposit_amount := 7#u64 }⟩,
        []) := by
  have hd : (s₁ treeA).data = .treeAccount tree := by rw [hT]
  have hv : UpdateDepositLimitAccountsValid toyD.toAddresses s₁ toyTx.toTxContext ⟨treeA, pk 1#u8⟩ tree := by
    refine ⟨⟨⟨by rw [hT], hd⟩, ?_, hauth⟩, by simp [toyTx]⟩
    show treeA = toyD.createProgramAddress (merkleTreeSeeds ++ [tree.bump])
    rw [hTb]; rfl
  show (do let s' ← execUpdateDepositLimit toyD s₁ toyTx ⟨treeA, pk 1#u8⟩ 7#u64; pure (s', [])) = _
  unfold execUpdateDepositLimit
  simp only [hd]
  rw [if_neg (not_not.mpr hv), hT]
  rfl

/-- The tree's authority after the toy `initialize` is the toy signer. -/
theorem toy_init_authority {s₁ : State} {tree : merkle_tree.MerkleTreeAccount}
    (hinit : execInitialize toyD toyS0 toyTx toyInitA = .ok s₁)
    (hT : s₁ treeA = ⟨1#u64, toyD.programId, .treeAccount tree⟩) :
    tree.authority = pk 1#u8 := by
  have hpid : toyD.programId ≠ systemProgram := by unfold toyD; decide +kernel
  have hdist := singleton_pdas_distinct_of _ _ _ toy_fixed_addresses
  obtain ⟨-, params, -, hI, -, hcfg, -⟩ :=
    init_between (rent := toyRent) hdist hpid rfl (toyTx_rentPositive _ rfl) (fun k h => toyGenesis k h.1) toyHashesAgree.zeroBytes_agree hinit
  have h1 := params.limitAuthority_init
  rw [hcfg, hI] at h1
  have h2 : toPubkey tree.authority = toPubkey (pk 1#u8) := by
    have htree : s₁.treeAccount toyD.treeAddress = tree := by
      show (match (s₁ treeA).data with | .treeAccount t => t | _ => _) = tree
      rw [hT]
    rw [← htree]
    exact h1
  simpa [fromPubkey_toPubkey] using congrArg fromPubkey h2

/-- **The hypotheses of `run_connection` and of the goals about runs hold with an admin change
    inside the run.** The execution `initialize`, `update_deposit_limit`, deposit satisfies every
    hypothesis of `run_connection` and initializes the pool, and every spec run of it
    (`IsRunOf`) records an admin change before its last transaction. -/
theorem toy_admin_change_nonvacuous :
    ∃ (s₀ s : State) (evs : List Event) (states : List State),
      Genesis toyD.programId s₀ ∧ ExecutionPath toyD s₀ evs states s ∧ ProgramNotSystem toyD ∧
      PairingLaws toyC.e ∧ HashesAgree toyD ∧ ExecutionAssumptions toyD evs ∧ ¬ AddressCollision toyD (proofsIn evs) ∧
      (∀ tx ix em, .program tx ix em ∈ evs → SameRent toyRent tx.minimumBalance) ∧ Initialized toyD s ∧
      ∀ params r, IsRunOf toyD toyRent s₀ evs states s params r → r.adminChangesUpTo r.txs.length ≠ [] := by
  obtain ⟨s₁, tree, token, config, hinit, hT, hK, hC, hP, hO, hshape, hroots, hsubs, hT0, hTn, hTb, -,
    hkb, hcb, hdr, hwr, hmr⟩ := toy_init_ok
  have hpid : toyD.programId ≠ systemProgram := by unfold toyD; decide +kernel
  obtain ⟨g1, g2, g3, g4, g5, -, -⟩ := addr_facts
  have h1 : step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, []) := by
    show (do let s' ← execInitialize toyD toyS0 toyTx toyInitA; pure (s', [])) = _
    rw [hinit]; rfl
  -- the admin change
  set tree₂ : merkle_tree.MerkleTreeAccount := { tree with max_deposit_amount := 7#u64 } with htree₂
  set s₂ := s₁.set treeA ⟨1#u64, toyD.programId, .treeAccount tree₂⟩ with hs₂
  have h2 : step toyD s₁ toyTx (.updateDepositLimit ⟨treeA, pk 1#u8⟩ 7#u64) = .ok (s₂, []) :=
    toy_admin_step hT hTb (toy_init_authority hinit hT)
  -- the deposit, from the state after the admin change
  have hO₂ : ∀ k, k ≠ treeA → k ≠ tokenA → k ≠ configA → k ≠ pk 1#u8 → s₂ k = toyS0 k :=
    fun k e1 e2 e3 e4 => by rw [hs₂, State.set_other _ _ e1]; exact hO k e1 e2 e3 e4
  obtain ⟨s₃, e₃, -, h3, -⟩ := toy_deposit_ok s₂ tree₂ token config (by rw [hs₂, State.set_same])
    (by rw [hs₂, State.set_other _ _ (Ne.symm g4)]; exact hK)
    (by rw [hs₂, State.set_other _ _ (Ne.symm g5)]; exact hC)
    (by rw [hs₂, State.set_other _ _ (Ne.symm g1)]; exact hP) hO₂
    hshape hroots hsubs hT0 hTn hTb (by show 2 ≤ (7#u64 : U64).val; decide) hkb hcb hdr hwr hmr
  -- the facts the deposit needs, from the toy deposit after `initialize`
  obtain ⟨-, -, -, -, -, -, -, -, solana, depCrypto, -⟩ := toy_execution
  -- the pool stays initialized
  have wf₁ := wf_reachable toyGenesis (.program h1 toyTx_rentPositive (.nil _)) hpid toyHashesAgree
  have wf₂ := wf_reachable toyGenesis (.program h1 toyTx_rentPositive (.program h2 toyTx_rentPositive (.nil _))) hpid toyHashesAgree
  obtain ⟨hi₁, -⟩ := init_between (rent := toyRent) (singleton_pdas_distinct_of _ _ _ toy_fixed_addresses)
    hpid rfl (toyTx_rentPositive _ rfl) (fun k h => toyGenesis k h.1) toyHashesAgree.zeroBytes_agree hinit
  obtain ⟨s₂', h2', h2e⟩ := PrivacyCash.Model.Except.bind_ok h2
  cases h2e
  obtain ⟨hi₂, -, -⟩ := udl_between (rent := toyRent) wf₁ hi₁ h2'
  have hi₃ := transact_initialized wf₂ hi₂ h3
  refine ⟨toyS0, s₃, _, _, toyGenesis,
    .program h1 toyTx_rentPositive (.program h2 toyTx_rentPositive (.program h3 toyTx_rentPositive (.nil _))), toyProgramNotSystem, toyLaws, toyHashesAgree,
    ExecutionFacts.toAssumptions ⟨toy_fixed_addresses, ?_⟩,
    toy_noCollision _ (by
      intro tx a proof ext fee out1 out2 em hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h <;> cases h; simp), ?_, hi₃, ?_⟩
  · intro tx ix em hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with hev | hev | hev <;> cases hev
    · trivial
    · trivial
    · exact ⟨solana, depCrypto⟩
  · intro tx ix em hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h <;> cases h <;> rfl
  · intro params r hr
    have htxs := hr.txs
    have hlen : r.txs.length = 1 := by rw [htxs]; rfl
    -- the deposit is event 2, after the admin instruction (event 1)
    rw [hlen, (hr.record (j := 0) (i := 2) rfl).2]
    simp [adminChangesBefore, List.range_succ, toAdminChange]

end Connection.Toy
