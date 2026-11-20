import Connection.Proofs.StepComplete
import Connection.Proofs.ToySpend
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Example transactions for completeness of `transact`

NOT FOR REVIEW: the statements are restated in `Connection/ConnectionTheorems.lean`
(`transact_complete_nonvacuous`) and `Connection/Findings.lean` (the counterexamples for L1 and
A0). In the state after `initialize`, the spec allows the deposit of the example code run, the
same deposit with `proof_a` the 64 zero bytes (A0), and an internal transfer (L1). -/

namespace Connection.Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha

/-- The A0 example's proof: the deposit's, with `proof_a` the 64 zero bytes. -/
abbrev a0Proof : transact.Proof := toyProof zeros64 two32
/-- The L1 example's proof: public amount 0. -/
abbrev l1Proof : transact.Proof := toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32

/-- The example deposit as sent (signers of `toyTx`, accounts `depA`, 2 lamports, no fee). -/
abbrev depTx : TransactTx := ⟨toyTx.toTxContext, depA, ⟨depProof, 2#i64, 0#u64, emptySlice, emptySlice⟩⟩
/-- The A0 example as sent: the deposit with `a0Proof`. -/
abbrev a0Tx : TransactTx := ⟨toyTx.toTxContext, depA, ⟨a0Proof, 2#i64, 0#u64, emptySlice, emptySlice⟩⟩
/-- The L1 example as sent: an internal transfer (amount 0, fee 0) with `l1Proof`. -/
abbrev l1Tx : TransactTx := ⟨toyTx.toTxContext, depA, ⟨l1Proof, 0#i64, 0#u64, emptySlice, emptySlice⟩⟩

/-- Every account of `toyS0` is an untouched system account. -/
theorem toyS0_plain (k : Pubkey) : (toyS0 k).owner = systemProgram ∧ (toyS0 k).data = .empty := by
  unfold toyS0; split_ifs <;> exact ⟨rfl, rfl⟩

/-- The example's transactions list the right accounts. -/
theorem depA_listed (pa : Std.Array U8 64#usize) (pubAmt : Std.Array U8 32#usize) :
    AccountsListed toyD depA (toyProof pa pubAmt) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Only the program's accounts and untouched system accounts -/

/-- `ProgramOrPlain d s`: every account is the program's (with one of its account types) or an
    untouched system account. Stronger than `PdasOnlyByProgram`; the example states satisfy it. -/
def ProgramOrPlain (d : Deployment) (s : State) : Prop :=
  ∀ k, ((s k).owner = d.programId ∧ (s k).data.isProgramData = true) ∨
    ((s k).owner = systemProgram ∧ (s k).data = .empty)

/-- An accepted `transact` keeps `ProgramOrPlain`: it only creates two nullifier accounts and
    rewrites the tree. -/
theorem programOrPlain_transact {d : Deployment} {s s' : State} {tx : TxEnv} {a : TransactAccounts}
    {proof : transact.Proof} {ext : I64} {fee : U64} {out1 out2 : Slice U8}
    {events : List CommitmentData} (h : ProgramOrPlain d s)
    (hx : execTransact d s tx a proof ext fee out1 out2 = .ok (s', events)) :
    ProgramOrPlain d s' := by
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, hvalid, hmb, hs₁, hhandler, hs', -⟩ := execTransact_ok hx
  obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨o0, d0, k0⟩ := initAccount_ownerData hA1
  obtain ⟨o1, d1, k1⟩ := initAccount_ownerData hA2
  have hs'k : ∀ k, (s' k).owner = (s₁ k).owner ∧
      (s' k).data = (if k = a.treeAccount then .treeAccount tree' else (s₁ k).data) := by
    intro k; rw [hs']
    by_cases hk : k = a.treeAccount
    · subst hk; simp [State.set, State.withBalances]
    · simp [State.set, hk, State.withBalances]
  have hown : ∀ k, (s k).owner = d.programId → (s₁ k).owner = d.programId := by
    intro k hk
    by_cases h1 : k = a.nullifier1
    · rw [h1]; exact o1
    rw [(k1 k h1).1]
    by_cases h0 : k = a.nullifier0
    · rw [h0]; exact o0
    rw [(k0 k h0).1]; exact hk
  intro k
  obtain ⟨e1, e2⟩ := hs'k k
  by_cases ht : k = a.treeAccount
  · left; rw [e1, e2, if_pos ht]
    exact ⟨hown k (ht ▸ hvalid.treeAccount.1.1), rfl⟩
  rw [e1, e2, if_neg ht]
  by_cases h1 : k = a.nullifier1
  · left; rw [h1]; exact ⟨o1, by rw [d1]; rfl⟩
  rw [(k1 k h1).1, (k1 k h1).2]
  by_cases h0 : k = a.nullifier0
  · left; rw [h0]; exact ⟨o0, by rw [d0]; rfl⟩
  rw [(k0 k h0).1, (k0 k h0).2]; exact h k

/-- The state after the example's `initialize` satisfies `ProgramOrPlain`. -/
theorem toy_init_programOrPlain {s₁ : State}
    (h1 : step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, [])) : ProgramOrPlain toyD s₁ := by
  obtain ⟨s₁', tree, token, config, hinit, hT, hK, hC, hP, hO, -⟩ := toy_init_ok
  have hinitStep : step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁', []) := by
    show (do let s' ← execInitialize toyD toyS0 toyTx toyInitA; pure (s', [])) = _
    rw [hinit]; rfl
  obtain rfl : s₁ = s₁' := (Prod.mk.inj (Except.ok.inj (h1.symm.trans hinitStep))).1
  intro k
  by_cases h1 : k = treeA
  · subst h1; rw [hT]; exact Or.inl ⟨rfl, rfl⟩
  by_cases h2 : k = tokenA
  · subst h2; rw [hK]; exact Or.inl ⟨rfl, rfl⟩
  by_cases h3 : k = configA
  · subst h3; rw [hC]; exact Or.inl ⟨rfl, rfl⟩
  by_cases h4 : k = pk 1#u8
  · subst h4; rw [hP]; exact Or.inr ⟨rfl, rfl⟩
  rw [hO k h1 h2 h3 h4]; exact Or.inr (toyS0_plain k)

set_option maxHeartbeats 2000000 in
/-- In the state after `initialize`, the hypotheses of completeness hold, and the spec allows the
    example deposit, the same deposit with `proof_a` the 64 zero bytes, and an internal transfer. -/
theorem toy_complete_examples :
    ∃ s₁ : State,
      Run toyD toyS0 [.program toyTx (.initialize toyInitA) []] s₁ ∧ Initialized toyD s₁ ∧
      PdasOnlyByProgram toyD s₁ ∧ SignerIsPlain s₁ depA ∧
      SpecAllows (d := toyD) toyC toyRent s₁ depTx ∧
      SpecAllows (d := toyD) toyC toyRent s₁ a0Tx ∧
      SpecAllows (d := toyD) toyC toyRent s₁ l1Tx := by
  withSyscallSpec toyC
  obtain ⟨s₁, tree, token, config, hinit, hT, hK, hC, hP, hO, -⟩ := toy_init_ok
  obtain ⟨s₁', s₂, e₂, h1, -, hpid, h2, -, depAssumptions, depAddressesDiffer, depRent⟩ := toy_run
  have hinitStep : step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, []) := by
    show (do let s' ← execInitialize toyD toyS0 toyTx toyInitA; pure (s', [])) = _
    rw [hinit]; rfl
  have es : s₁' = s₁ := (Prod.mk.inj (Except.ok.inj (h1.symm.trans hinitStep))).1
  rw [es] at h2
  have hrun : Run toyD toyS0 [.program toyTx (.initialize toyInitA) []] s₁ :=
    .program hinitStep toyTx_rentPositive (.nil _)
  have pre₀ : SpecAllows (d := toyD) toyC toyRent s₁ depTx :=
    (transact_connection_pf ⟨_, _, toyGenesis, hrun⟩ hpid (.program h2 toyTx_rentPositive (.nil _)) toyC toyLaws
      toyHashesAgree depAssumptions depAddressesDiffer depRent).1
  refine ⟨s₁, hrun, ?_, ?_, ?_, pre₀, ?_, ?_⟩
  · exact ⟨⟨tree, by unfold HoldsTree; rw [show toyD.treeAddress = treeA from rfl, hT]; exact ⟨rfl, rfl⟩⟩,
     ⟨token, by unfold HoldsTreeToken; rw [show toyD.poolAddress = tokenA from rfl, hK]; exact ⟨rfl, rfl⟩⟩,
     ⟨config, by unfold HoldsGlobalConfig; rw [show toyD.configAddress = configA from rfl, hC]; exact ⟨rfl, rfl⟩⟩⟩
  · exact fun _ => toy_init_programOrPlain hinitStep _
  · show (s₁ (pk 1#u8)).owner = systemProgram ∧ (s₁ (pk 1#u8)).data.isEmpty
    rw [hP]; exact ⟨rfl, rfl⟩
  · -- A0: only the proof check differs from the deposit
    unfold SpecAllows at pre₀ ⊢
    obtain ⟨kR, eB, mF, pA, vZ, nN, dN, nA, dL, pS, sS, sSig, sNP, tN, aR, eL, pNR, cI, bF, -⟩ := pre₀
    have hdec := decode_toInputs (signers := toyTx.signers) toyC a0Proof depA 2#i64 0#u64
      emptySlice emptySlice toy_zeros_decodes rfl toy_zeros_decodes
    exact @Spec.transactPreconditions.mk _ (syscallGroups toyC) (inferInstanceAs (AddCommGroup Unit))
      (inferInstanceAs (Module Spec.F Unit)) (inferInstanceAs (CommGroup Unit))
      (syscallPairing toyC) (programDeployment toyC) _ _
      kR eB mF pA ⟨_, hdec, rfl⟩
      nN dN nA dL
      pS sS sSig sNP
      tN aR eL pNR cI
      bF (by unfold Spec.mintIsSol; rfl)
  · -- L1: amount 0, fee 0, public amount 0
    unfold SpecAllows at pre₀ ⊢
    obtain ⟨kR, eB, mF, pA, vZ, nN, dN, nA, dL, pS, sS, sSig, sNP, tN, aR, eL, pNR, cI, bF, -⟩ := pre₀
    have he : (toInputs l1Tx).extAmt = 0 := by
      simp [toInputs]
    have hf : (toInputs l1Tx).f = 0 := by
      simp [toInputs]
    have hbal : ∀ k, (s₁ k).lamports.val ≤ 1000 := by
      intro k
      by_cases h1 : k = treeA
      · subst h1; rw [hT]; simp
      by_cases h2 : k = tokenA
      · subst h2; rw [hK]; simp
      by_cases h3 : k = configA
      · subst h3; rw [hC]; simp
      by_cases h4 : k = pk 1#u8
      · subst h4; rw [hP]; simp
      rw [hO k h1 h2 h3 h4]; unfold toyS0; split_ifs <;> simp [Account.default]
    have ht : ∀ i, (toWorld toyD toyRent s₁).nullifierTopUp
        (toInputs l1Tx) i ≤ 1 :=
      fun i => Nat.sub_le _ _
    have hsolv : Spec.signerSolvent (toWorld toyD toyRent s₁).balances
        (toInputs l1Tx).s 2
        ((toWorld toyD toyRent s₁).nullifierTopUp
          (toInputs l1Tx) 0 +
        (toWorld toyD toyRent s₁).nullifierTopUp
          (toInputs l1Tx) 1) :=
      sS
    have hdec := decode_toInputs (signers := toyTx.signers) toyC l1Proof depA 0#i64 0#u64
      emptySlice emptySlice toy_alpha_decodes rfl toy_zeros_decodes
    obtain ⟨a0, a1⟩ := newNullifierAccount_toWorld toyD toyRent s₁ toyTx.signers depA l1Proof 0#i64 0#u64
      emptySlice emptySlice
    obtain ⟨b0, b1⟩ := newNullifierAccount_toWorld toyD toyRent s₁ toyTx.signers depA depProof 2#i64 0#u64
      emptySlice emptySlice
    have nA' : Spec.nullifierAccountsCreatable (toWorld toyD toyRent s₁).state
        (toInputs l1Tx) := by
      unfold Spec.nullifierAccountsCreatable at nA ⊢
      rw [a0, a1]; rw [b0, b1] at nA; exact nA
    have sNP' : Spec.signerNotPoolNotNullifiers
        (toInputs l1Tx)
        (toWorld toyD toyRent s₁).state := by
      unfold Spec.signerNotPoolNotNullifiers at sNP ⊢
      rw [a0, a1]; rw [b0, b1] at sNP; exact sNP
    refine @Spec.transactPreconditions.mk _ (syscallGroups toyC) (inferInstanceAs (AddCommGroup Unit))
      (inferInstanceAs (Module Spec.F Unit)) (inferInstanceAs (CommGroup Unit))
      (syscallPairing toyC) (programDeployment toyC) _ _
      kR ?_ ?_ ?_ ⟨_, hdec, rfl⟩
      nN dN nA' ?_
      ?_ ?_ sSig sNP'
      tN ?_ eL ?_ ?_ ?_ (by unfold Spec.mintIsSol; rfl)
    · unfold Spec.externalDataBound Spec.externalDataHash
      rw [toy_extDataHash]; rfl
    · unfold Spec.feeSufficient; rw [he, hf]; simp
    · unfold Spec.pubAmtConsistent; rw [he, hf]
      refine ⟨fun h => by omega, ?_⟩
      show toF zeros32 = _; rw [toF_zeros32]; simp
    · intro h; rw [he] at h; omega
    · unfold Spec.poolSolvent; rw [he, hf]
      exact ⟨fun h => by omega, fun h => by omega⟩
    · unfold Spec.signerSolvent at hsolv ⊢
      rw [he]; simp at hsolv ⊢; omega
    · unfold Spec.amountsInRange; rw [he, hf]; norm_num
    · exact ⟨fun h => by rw [he] at h; omega, fun h => by rw [hf] at h; omega⟩
    · intro i
      show Spec.canonicalEncoding (toBytes ((publicInputs _)[i.val]!).val) _
      rw [canonicalEncoding_iff]
      fin_cases i
      · exact ⟨canonical_one32, rfl⟩
      · exact ⟨canonical_zeros32, rfl⟩
      · exact ⟨canonical_zeros32, rfl⟩
      · exact ⟨canonical_zeros32, rfl⟩
      · exact ⟨canonical_one32, rfl⟩
      · exact ⟨canonical_zeros32, rfl⟩
      · exact ⟨canonical_zeros32, rfl⟩
    · refine ⟨fun k _ => ?_, fun h => by rw [he] at h; omega⟩
      have hb : (toWorld toyD toyRent s₁).balances k ≤ 1000 := hbal _
      have h0 := ht 0
      have h1 := ht 1
      unfold Spec.balanceDelta
      rw [he, hf]
      split_ifs <;> push_cast <;> omega

end Connection.Toy
