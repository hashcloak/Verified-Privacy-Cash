import Connection.Proofs.StepComplete
import Connection.Proofs.ToySpend
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Toy execution for G3a and G3b for the code

NOT FOR REVIEW: the statement is restated in `Connection/CodeModelStatements.lean`. -/

namespace Connection.Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha

/-- The deposit's witness for G3: as `depWit`, but its zero-amount inputs have commitment `1`, so
    they don't share a commitment and position with the withdrawal's inputs (commitment `0`). -/
def depWitG3 : LeanSpec.Witness where
  mint := 0
  inAmt := 0
  inSk := ![-2, -1]
  inR := ![3, 2]
  openings := fun _ => ⟨0, 0⟩
  outAmt := ![2, 0]
  outPk := ![2, 0]
  outR := ![-4, 0]

theorem depG3_relation :
    LeanSpec.RelationS (toInputs toyTx.signers depA depProof 2#i64 0#u64 emptySlice emptySlice).pubInputs depWitG3 where
  outputCommitmentIntegrity := by
    intro j
    fin_cases j <;>
      simp [toInputs, LeanSpec.TxInputs.pubInputs, depProof, toyProof, toF_zeros32, depWitG3,
        LeanSpec.commit, toy_H4]
    all_goals norm_num
  nullifierCorrectness := by
    intro i
    fin_cases i <;>
      simp [toInputs, LeanSpec.TxInputs.pubInputs, depProof, toyProof, toF_zeros32, toF_one32, depWitG3,
        LeanSpec.nullifier, LeanSpec.Witness.sign, LeanSpec.signature, LeanSpec.Witness.inC,
        LeanSpec.commit, LeanSpec.Witness.inPk, toy_H1, toy_H3, toy_H4]
    all_goals ring
  noDuplicateNullifiers := by
    simp only [toInputs, LeanSpec.TxInputs.pubInputs, Matrix.cons_val_zero, Matrix.cons_val_one]
    show toF zeros32 ≠ toF one32
    rw [toF_zeros32, toF_one32]; decide
  correctOpenings := by intro i hi; simp [depWitG3] at hi
  amountConservation := by
    simp [toInputs, LeanSpec.TxInputs.pubInputs, depProof, toyProof, toF_two32, depWitG3]
  outputRangeChecks := by
    haveI : Fact (1 < LeanSpec.p) := ⟨by norm_num [LeanSpec.p]⟩
    have hval : ZMod.val (2 : LeanSpec.F) = 2 := by
      have := ZMod.val_natCast_of_lt (n := LeanSpec.p) (a := 2) (by norm_num [LeanSpec.p]); exact_mod_cast this
    intro j; fin_cases j <;> simp [depWitG3, hval]

section
variable [LeanSpec.Groups] [AddCommGroup LeanSpec.G1] [Module LeanSpec.F LeanSpec.G1]
  [AddCommGroup LeanSpec.G2] [Module LeanSpec.F LeanSpec.G2] [CommGroup LeanSpec.GT]
  [LeanSpec.Pairing] [LeanSpec.Deployment]

/-- No input of the deposit shares a commitment with an input of the withdrawal. -/
theorem withdrawal_inputs_unused {w0 : LeanSpec.World} (r : LeanSpec.Run w0) (i : Fin 2) :
    ¬ LeanSpec.InputUsedInRun r (fun _ => depWitG3) spendWit i := by
  rintro ⟨j, _, e, hC, _⟩
  have h1 : depWitG3.inC e = 1 := by
    fin_cases e <;> simp [depWitG3, LeanSpec.Witness.inC, LeanSpec.commit, LeanSpec.Witness.inPk, toy_H1, toy_H4]
    all_goals norm_num
  have h0 : spendWit.inC i = 0 := by
    fin_cases i <;> simp [spendWit, LeanSpec.Witness.inC, LeanSpec.commit, LeanSpec.Witness.inPk, toy_H1, toy_H4]
    all_goals norm_num
  have : (1 : LeanSpec.F) = 0 := h1.symm.trans (hC.trans h0)
  exact absurd this (by decide)

end

section
attribute [local instance] toySpecGroups toySpecG1Group toySpecG2Group toySpecG1Module
  toySpecG2Module toySpecGTGroup toySpecPairing toySpecDeployment

/-- **The hypotheses of G3a and G3b for the code hold together, on a real spend, for every way to
    withdraw, and the code accepts it.** After `initialize` and a deposit of 2 lamports, with
    nothing changed since, for every way to withdraw 2 lamports, the withdrawal spending the
    deposit's note with that split satisfies every hypothesis of both, and `step` accepts it. -/
theorem toy_G3_code_nonvacuous (h64 : Usize.max = 2 ^ 64 - 1) :
    ∃ (s₀ s : State) (evs : List Event)
      (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params))
      (wit : ℕ → LeanSpec.Witness),
      Genesis toyD.programId s₀ ∧ Run toyD s₀ evs s ∧ DeploymentFacts toyD
      ∧ PairingLaws toyC.e ∧ HashesAgree toyD.crypto ∧ CompletenessAssumptions toyD.crypto toyC
      ∧ toWorld toyD toyRent s = r.final
      ∧ r.WitnessesFor wit
      ∧ ∀ payout feeAmount : ℕ, LeanSpec.Goals.WithdrawalWay r.final.state.config 2 payout feeAmount →
        ∃ (tx : TxEnv) (a : TransactAccounts) (proof : transact.Proof) (ext : I64) (fee : U64)
          (out1 out2 : Slice U8) (tree : merkle_tree.MerkleTreeAccount) (tt : admin.TreeTokenAccount)
          (config : admin.GlobalConfig) (witness : LeanSpec.Witness) (k : ℕ),
          let inputs := toInputs tx.signers a proof ext fee out1 out2
          ReachesProgram toyD toyRent s tx a proof ext fee out1 out2 tree tt config
          ∧ ext.val ≠ 0 ∧ proof.proof_a.val ≠ List.replicate 64 0#u8
          ∧ LeanSpec.HonestSpend r wit inputs witness k
          ∧ LeanSpec.LimitsNotHit r.final inputs
          ∧ witness.inAmt 0 ≠ 0
          ∧ witness.inAmt 0 + witness.inAmt 1 = ((2 : ℕ) : LeanSpec.F)
          ∧ inputs.extAmt = -(payout : ℤ) ∧ inputs.f = feeAmount
          ∧ ∃ s' events, step toyD s tx (.transact a proof ext fee out1 out2) = .ok (s', events) := by
  obtain ⟨s₁', s₂', e₂', h1', -, hpid, h2', -, solana, depCrypto, depOutside⟩ := toy_execution
  have hi₁ : Initialized toyD s₁' := by
    obtain ⟨s₁, -, -, -, -, h1, -, -, hi, -, -⟩ := toy_spend_execution toySplit_one
    rwa [(Prod.mk.inj (Except.ok.inj (h1.symm.trans h1'))).1] at hi
  have hrun₁ : Run toyD toyS0 [.program toyTx (.initialize toyInitA) []] s₁' := .program h1' toyTx_rentPositive (.nil _)
  have hpath₁ : ExecutionPath toyD toyS0 [.program toyTx (.initialize toyInitA) []] [s₁'] s₁' :=
    .program h1' toyTx_rentPositive (.nil _)
  have hrun₂ : Run toyD toyS0 [.program toyTx (.initialize toyInitA) [],
      .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂'] s₂' :=
    .program h1' toyTx_rentPositive (.program h2' toyTx_rentPositive (.nil _))
  have wf₂ := wf_reachable toyGenesis hrun₂ hpid toyHashesAgree
  -- the run after `initialize`
  have assume₁ : ExecutionAssumptions toyD toyS0 [.program toyTx (.initialize toyInitA) []] := by
    refine ⟨toy_fixed_addresses, ?_⟩
    intro pre post s tx ix em hsplit _
    rcases pre with _ | ⟨x, pre⟩
    · simp only [List.nil_append, List.cons.injEq] at hsplit
      obtain ⟨h, -⟩ := hsplit
      cases h
      trivial
    · simp at hsplit
  have outside₁ : ∀ tx ix em, Event.program tx ix em ∈ [Event.program toyTx (.initialize toyInitA) []] →
      SameRent toyRent tx := by
    intro tx ix em hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    cases hm
    rfl
  have hspec := execution_is_spec_run_pf toyGenesis hpath₁ hpid toyC toyLaws toyHashesAgree assume₁
    outside₁
  rcases hspec with ⟨hno, -⟩ | ⟨params, r₀, -, -, -, -, -, -, htx₀, -, -, -, -, -, -, b₀, hb₀, -, hw₀⟩
  · obtain ⟨⟨t, ht⟩, -⟩ := hi₁
    exact absurd ht (hno.1 _ t)
  -- the deposit extends it
  have hdep : LeanSpec.transact (toInputs toyTx.signers depA depProof 2#i64 0#u64 emptySlice emptySlice)
      (toWorld toyD toyRent s₁') (toWorld toyD toyRent s₂') :=
    transact_connection_pf toyGenesis hrun₁ hpid (.program h2' toyTx_rentPositive (.nil _)) toyC toyLaws toyHashesAgree solana depCrypto.1 depCrypto.2 depOutside
  rw [hw₀] at hdep
  obtain ⟨r, hrtx, hrf, -⟩ := r₀.snoc b₀ hb₀ _ _ hdep
  have htx₀' : r₀.txs = [] := by rw [htx₀]; simp [runTxs, stepTxs]
  have hrtx' : r.txs = [toInputs toyTx.signers depA depProof 2#i64 0#u64 emptySlice emptySlice] := by
    rw [hrtx, htx₀']; rfl
  have hfinal : toWorld toyD toyRent s₂' = r.final := hrf.symm
  refine ⟨toyS0, s₂', _, params, r, fun _ => depWitG3, toyGenesis, hrun₂, toyDeploymentFacts, toyLaws,
    toyHashesAgree, toyAssumptions h64, hfinal, ?_, fun payout feeAmount hway => ?_⟩
  · intro j hj _
    rw [List.getElem_of_eq hrtx' hj]
    have hj1 : j = 0 := by rw [hrtx'] at hj; simpa using hj
    subst hj1
    exact depG3_relation
  -- the split: 1 and 1, or 2 and 0
  obtain ⟨ext, fee, hsplit, hext, hfee⟩ : ∃ (ext : I64) (fee : U64), ToySplit ext fee ∧
      ext.val = -(payout : ℤ) ∧ fee.val = feeAmount := by
    obtain ⟨h0, hsum, -⟩ := hway
    rcases (show (payout = 1 ∧ feeAmount = 1) ∨ (payout = 2 ∧ feeAmount = 0) by omega)
      with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, _, toySplit_one, wdExt_val, by simp⟩
    · exact ⟨_, _, toySplit_two, by simp, by simp⟩
  -- the withdrawal with that split, after the same `initialize` and deposit
  obtain ⟨s₁, s₂, s₃, e₂, e₃, h1, h2, h3, -, crypto, outside, hsysS⟩ := toy_spend_execution hsplit
  have es₁ : s₁' = s₁ := (Prod.mk.inj (Except.ok.inj (h1'.symm.trans h1))).1
  subst es₁
  have es₂ : (s₂', e₂') = (s₂, e₂) := Except.ok.inj (h2'.symm.trans h2)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj es₂
  -- the withdrawal's preconditions
  have hpre0 : LeanSpec.transactPreconditions (toInputs toyTx.signers spendA spendProof ext fee emptySlice emptySlice)
      (toWorld toyD toyRent s₂') :=
    (transact_connection_pf toyGenesis hrun₂ hpid (.program h3 toyTx_rentPositive (.nil _)) toyC toyLaws toyHashesAgree solana crypto.1 crypto.2 outside).1
  have hpre : LeanSpec.transactPreconditions (toInputs toyTx.signers spendA spendProof ext fee emptySlice emptySlice) r.final := by
    rw [← hfinal]; exact hpre0
  -- getting past Anchor
  have hx : execTransact toyD s₂' toyTx spendA spendProof ext fee emptySlice emptySlice = .ok (s₃, e₃) := h3
  obtain ⟨tree, tt, config, mb, sB, env', tree', ap, hvalid, hmb, hsB, -⟩ := execTransact_ok hx
  have hmbr : toyRent = mb := Option.some.inj hmb
  subst hmbr
  have hnr : 0 < (toyRent nullifierAccountSpace).val := toyTx_rentPositive toyRent rfl nullifierAccountSpace
  obtain ⟨sA, hA1, -⟩ := Option.bind_eq_some_iff.mp hsB
  have hnf0 : spendA.nullifier0 = toyD.pda (nullifier0Seeds spendProof.input_nullifiers.val[0]!) := hvalid.nullifier0.1
  have hsn0 : spendA.signer ≠ spendA.nullifier0 := fun e =>
    solana.pdasDoNotSign _ (by rw [← hnf0, ← e]; exact hvalid.signer)
  have hnf1 : spendA.nullifier1 = toyD.pda (nullifier1Seeds spendProof.input_nullifiers.val[1]!) := hvalid.nullifier1.1
  have hnf2 : spendA.nullifier2 = toyD.pda (nullifier0Seeds spendProof.input_nullifiers.val[1]!) := hvalid.nullifier2.1
  have hnf3 : spendA.nullifier3 = toyD.pda (nullifier1Seeds spendProof.input_nullifiers.val[0]!) := hvalid.nullifier3.1
  have htreeAddr := (wf₂.tree _ _ hvalid.treeAccount.1).1
  have hpoolAddr := wf₂.pool _ _ hvalid.treeTokenAccount.1
  have hcfgAddr := (wf₂.config _ _ hvalid.globalConfig.1).1
  have reach : ReachesProgram toyD toyRent s₂' toyTx spendA spendProof ext fee emptySlice emptySlice tree tt config := {
    accounts := {
      tree := htreeAddr, pool := hpoolAddr, config := hcfgAddr
      nullifier0 := hnf0, nullifier1 := hnf1, nullifier2 := hnf2, nullifier3 := hnf3
      systemProg := hvalid.systemProgram
      signerPlain := hsysS }
    program := {
      tree := by rw [← htreeAddr]; exact hvalid.treeAccount
      pool := by rw [← hpoolAddr]; exact hvalid.treeTokenAccount
      config := by rw [← hcfgAddr]; exact hvalid.globalConfig }
    nullifiers := {
      new0 := by rw [← hnf0]; exact hvalid.nullifier0.2
      new1 := by rw [← hnf1]; exact hvalid.nullifier1.2
      other0 := by rw [← hnf2]; exact hvalid.nullifier2.2
      other1 := by rw [← hnf3]; exact hvalid.nullifier3.2 }
    sameRent := hmb
    rentPositive := toyTx_rentPositive
    solana := solana }
  refine ⟨toyTx, spendA, spendProof, ext, fee, emptySlice, emptySlice, tree, tt, config, spendWit, 2,
    reach, by rcases hsplit with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide, alpha_ne_zeros, ?_, ?_, ?_, ?_, hext, hfee, ⟨_, _, h3⟩⟩
  · exact {
      genuine := by
        intro i hne
        fin_cases i
        · exact ⟨by show 0 < 2; norm_num, rfl, rfl, rfl, rfl⟩
        · exact absurd rfl hne
      notDoubleSpend := fun h => h.2.1 rfl
      inputNotUsedBefore := fun i => withdrawal_inputs_unused r i
      root := {
        isPrefix := by rw [hrtx']; simp
        isPrefixRoot := by
          have hcap : (r.firstLeaves 2).length < 2^26 :=
            (List.length_take_le _ _).trans_lt (by norm_num)
          rw [(LeanSpec.foldAppend_spec _ hcap).2.1, LeanSpec.treeHash.eq_2]
          show toF one32 = 1
          exact toF_one32 }
      circuit := spend_relation
      wellFormed := ⟨hpre.validZKP, hpre.externalDataBinding, hpre.pubAmtConsistency, hpre.amountRange,
        hpre.encOutLength, hpre.canonicalInputs, hpre.poolNotRecipient, hpre.signerSignature⟩
      signerCanPay := hpre.signerSolvency
      signerNotPoolNotNullifiers := hpre.signerNotPoolNotNullifiers }
  · refine ⟨?_, hpre.treeNotFull, hpre.balancesFit, hpre.minimumFee, hpre.depositLimit⟩
    have h := hpre.knownRoot.2.2.1
    rw [(hpre.canonicalInputs 0).2.2] at h
    exact h
  · show spendWit.inAmt 0 ≠ 0
    simp only [spendWit, Matrix.cons_val_zero]; decide
  · show spendWit.inAmt 0 + spendWit.inAmt 1 = _
    simp [spendWit]

end

end Connection.Toy
