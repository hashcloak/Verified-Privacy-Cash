import Connection.Proofs.StepComplete
import Connection.Proofs.ToyComplete
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Example code run for G3a and G3b for the code

NOT FOR REVIEW: the statement is restated in `Connection/CodeModelStatements.lean`. -/

namespace Connection.Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha

/-- The deposit's witness for G3: as `depWit`, but its zero-amount inputs have commitment `1`, so
    they don't share a commitment and position with the withdrawal's inputs (commitment `0`). -/
def depWitG3 : Spec.Witness where
  mint := 0
  inAmt := 0
  inSk := ![-2, -1]
  inR := ![3, 2]
  openings := fun _ => ⟨0, 0⟩
  outAmt := ![2, 0]
  outPk := ![2, 0]
  outR := ![-4, 0]

theorem depG3_relation :
    Spec.RelationS (toInputs ⟨⟨toyTx.signers⟩, depA, ⟨depProof, 2#i64, 0#u64, emptySlice, emptySlice⟩⟩).pubInputs depWitG3 where
  outputCommitmentIntegrity := by
    intro j
    fin_cases j <;>
      simp [toInputs, Spec.TxInputs.pubInputs, depProof, toyProof, toF_zeros32, depWitG3,
        Spec.commit, toy_H4]
    all_goals norm_num
  nullifierCorrectness := by
    intro i
    fin_cases i <;>
      simp [toInputs, Spec.TxInputs.pubInputs, depProof, toyProof, toF_zeros32, toF_one32, depWitG3,
        Spec.nullifier, Spec.Witness.sign, Spec.signature, Spec.Witness.inC,
        Spec.commit, Spec.Witness.inPk, toy_H1, toy_H3, toy_H4]
    all_goals ring
  noDuplicateNullifiers := by
    simp only [toInputs, Spec.TxInputs.pubInputs, Matrix.cons_val_zero, Matrix.cons_val_one]
    show toF zeros32 ≠ toF one32
    rw [toF_zeros32, toF_one32]; decide
  correctOpenings := by intro i hi; simp [depWitG3] at hi
  amountConservation := by
    simp [toInputs, Spec.TxInputs.pubInputs, depProof, toyProof, toF_two32, depWitG3]
  outputRangeChecks := by
    haveI : Fact (1 < Spec.p) := ⟨by norm_num [Spec.p]⟩
    have hval : ZMod.val (2 : Spec.F) = 2 := by
      have := ZMod.val_natCast_of_lt (n := Spec.p) (a := 2) (by norm_num [Spec.p]); exact_mod_cast this
    intro j; fin_cases j <;> simp [depWitG3, hval]

section
variable [Spec.Groups] [AddCommGroup Spec.G1] [Module Spec.F Spec.G1]
  [CommGroup Spec.GT]
  [Spec.Pairing] [Spec.Deployment]

/-- No input of the deposit shares a commitment with an input of the withdrawal. -/
theorem withdrawal_inputs_unused {w0 : Spec.World} (r : Spec.Run w0) (i : Fin 2) :
    ¬ Spec.InputUsedInRun r (fun _ => depWitG3) spendWit i := by
  rintro ⟨j, _, e, hC, _⟩
  have h1 : depWitG3.inC e = 1 := by
    fin_cases e <;> simp [depWitG3, Spec.Witness.inC, Spec.commit, Spec.Witness.inPk, toy_H1, toy_H4]
    all_goals norm_num
  have h0 : spendWit.inC i = 0 := by
    fin_cases i <;> simp [spendWit, Spec.Witness.inC, Spec.commit, Spec.Witness.inPk, toy_H1, toy_H4]
    all_goals norm_num
  have : (1 : Spec.F) = 0 := h1.symm.trans (hC.trans h0)
  exact absurd this (by decide)

end

section
attribute [local instance] toySpecGroups toySpecG1Group toySpecG1Module
  toySpecGTGroup toySpecPairing toySpecDeployment

/-- **The hypotheses of G3a and G3b for the code hold together, on a real spend, for every way to
    withdraw, and the code accepts it.** After `initialize` and a deposit of 2 lamports, with
    nothing changed since, for every way to withdraw 2 lamports, the withdrawal spending the
    deposit's note with that split satisfies every hypothesis of both, and `step` accepts it. -/
theorem toy_G3_code_nonvacuous (h64 : Usize.max = 2 ^ 64 - 1) :
    ∃ (s : State)
      (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params))
      (wit : ℕ → Spec.Witness),
      Reachable toyD s ∧ ProgramNotSystem toyD
      ∧ PairingLaws toyC.e ∧ HashesAgree toyD ∧ CryptoSucceeds toyD.crypto toyC ∧ RuntimeFacts toyRent
      ∧ PdasOnlyByProgram toyD s ∧ Initialized toyD s
      ∧ toWorld toyD toyRent s = r.final
      ∧ r.WitnessesFor wit
      ∧ ∀ payout feeAmount : ℕ, Spec.Goals.WithdrawalWay r.final.state.config 2 payout feeAmount →
        ∃ (tx : TransactTx) (sysvarRent : Option (Nat → U64)) (witness : Spec.Witness) (k : ℕ),
          let inputs := toInputs tx
          ReachesProgram toyD s tx.accounts tx.args.proof ∧ SameRent toyRent sysvarRent
          ∧ tx.args.extAmount.val ≠ 0 ∧ tx.args.proof.proof_a.val ≠ List.replicate 64 0#u8
          ∧ Spec.HonestSpend r wit inputs witness k
          ∧ Spec.LimitsNotHit r.final inputs
          ∧ witness.inAmt 0 ≠ 0
          ∧ witness.inAmt 0 + witness.inAmt 1 = ((2 : ℕ) : Spec.F)
          ∧ inputs.extAmt = -(payout : ℤ) ∧ inputs.f = feeAmount
          ∧ Accepts toyD s (tx.env sysvarRent) tx.instruction := by
  obtain ⟨s₁', s₂', e₂', h1', -, hpid, h2', -, depAssumptions, depAddressesDiffer, depOutside⟩ := toy_run
  have hi₁ : Initialized toyD s₁' := by
    obtain ⟨s₁, -, -, -, -, h1, -, -, hi, -, -⟩ := toy_spend_run toySplit_one
    rwa [(Prod.mk.inj (Except.ok.inj (h1.symm.trans h1'))).1] at hi
  have hrun₁ : Run toyD toyS0 [.program toyTx (.initialize toyInitA) []] s₁' := .program h1' toyTx_rentPositive (.nil _)
  have hpath₁ : CodeRun toyD toyS0 [⟨toyS0, .program toyTx (.initialize toyInitA) [], s₁'⟩] s₁' :=
    .program h1' toyTx_rentPositive (.nil _)
  have hrun₂ : Run toyD toyS0 [.program toyTx (.initialize toyInitA) [],
      .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂'] s₂' :=
    .program h1' toyTx_rentPositive (.program h2' toyTx_rentPositive (.nil _))
  have wf₂ := wf_reachable toyGenesis hrun₂ hpid toyHashesAgree
  -- the run after `initialize`
  have runFacts₁ : RunFacts toyD [.program toyTx (.initialize toyInitA) []] := by
    refine ⟨toy_fixed_addresses, ?_⟩
    intro tx ix em hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    cases hm
    trivial
  have outside₁ : ∀ tx ix em, Event.program tx ix em ∈ [Event.program toyTx (.initialize toyInitA) []] →
      SameRent toyRent tx.minimumBalance := by
    intro tx ix em hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    cases hm
    rfl
  have hspec := code_run_is_spec_run_pf toyGenesis hpath₁ hpid toyC toyLaws toyHashesAgree runFacts₁
    outside₁
  rcases hspec with ⟨hno, -⟩ | ⟨params, r₀, hr₀⟩
  · obtain ⟨⟨t, ht⟩, -⟩ := hi₁
    exact absurd ht (hno.1 _ t)
  have htx₀ := hr₀.txs
  obtain ⟨b₀, hb₀, -, hw₀⟩ := hr₀.final
  -- the deposit extends it
  have hdep : Spec.transact (toInputs ⟨⟨toyTx.signers⟩, depA, ⟨depProof, 2#i64, 0#u64, emptySlice, emptySlice⟩⟩)
      (toWorld toyD toyRent s₁') (toWorld toyD toyRent s₂') :=
    transact_connection_pf ⟨_, _, toyGenesis, hrun₁⟩ hpid (.program h2' toyTx_rentPositive (.nil _)) toyC toyLaws toyHashesAgree
      depAssumptions depAddressesDiffer depOutside
  rw [hw₀] at hdep
  obtain ⟨r, hrtx, hrf, -⟩ := r₀.snoc b₀ hb₀ _ _ hdep
  have htx₀' : r₀.txs = [] := by rw [htx₀]; simp [eventsOf, runTxs, stepTxs]
  have hrtx' : r.txs = [toInputs ⟨⟨toyTx.signers⟩, depA, ⟨depProof, 2#i64, 0#u64, emptySlice, emptySlice⟩⟩] := by
    rw [hrtx, htx₀']; rfl
  have hfinal : toWorld toyD toyRent s₂' = r.final := hrf.symm
  refine ⟨s₂', params, r, fun _ => depWitG3, ⟨_, _, toyGenesis, hrun₂⟩, toyProgramNotSystem, toyLaws,
    toyHashesAgree, toyCryptoSucceeds, toyRuntime h64,
    fun _ => programOrPlain_transact (toy_init_programOrPlain h1') h2' _, ?_, hfinal, ?_,
    fun payout feeAmount hway => ?_⟩
  · obtain ⟨s₁, s₂, s₃, e₂, e₃, h1, h2, h3, -⟩ := toy_spend_run toySplit_one
    have es₁ : s₁' = s₁ := (Prod.mk.inj (Except.ok.inj (h1'.symm.trans h1))).1
    subst es₁
    have es₂ : (s₂', e₂') = (s₂, e₂) := Except.ok.inj (h2'.symm.trans h2)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj es₂
    obtain ⟨tree, tt, config, -, -, -, -, -, hvalid, -⟩ :=
      execTransact_ok (show execTransact toyD s₂' toyTx spendA spendProof _ _ emptySlice emptySlice = .ok (s₃, e₃) from h3)
    exact ⟨⟨tree, hvalid.treeAccount.1⟩, ⟨tt, hvalid.treeTokenAccount.1⟩, ⟨config, hvalid.globalConfig.1⟩⟩
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
  obtain ⟨s₁, s₂, s₃, e₂, e₃, h1, h2, h3, -, ⟨spendAddressesDiffer, spendDistinctNullifiers⟩, outside, hsysS⟩ := toy_spend_run hsplit
  have es₁ : s₁' = s₁ := (Prod.mk.inj (Except.ok.inj (h1'.symm.trans h1))).1
  subst es₁
  have es₂ : (s₂', e₂') = (s₂, e₂) := Except.ok.inj (h2'.symm.trans h2)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj es₂
  -- the withdrawal's preconditions
  have hpre0 : Spec.transactPreconditions (toInputs ⟨⟨toyTx.signers⟩, spendA, ⟨spendProof, ext, fee, emptySlice, emptySlice⟩⟩)
      (toWorld toyD toyRent s₂') :=
    (transact_connection_pf ⟨_, _, toyGenesis, hrun₂⟩ hpid (.program h3 toyTx_rentPositive (.nil _)) toyC toyLaws toyHashesAgree
      ⟨depAssumptions.pdasDoNotSign, spendDistinctNullifiers⟩ spendAddressesDiffer outside).1
  have hpre : Spec.transactPreconditions (toInputs ⟨⟨toyTx.signers⟩, spendA, ⟨spendProof, ext, fee, emptySlice, emptySlice⟩⟩) r.final := by
    rw [← hfinal]; exact hpre0
  have reach : ReachesProgram toyD s₂' spendA spendProof :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, hsysS⟩
  refine ⟨⟨toyTx.toTxContext, spendA, ⟨spendProof, ext, fee, emptySlice, emptySlice⟩⟩, toyTx.minimumBalance,
    spendWit, 2,
    reach, rfl, by rcases hsplit with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide, alpha_ne_zeros, ?_, ?_, ?_, ?_, hext, hfee, ⟨_, _, h3⟩⟩
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
          rw [(Spec.foldAppend_spec _ hcap).2.1, Spec.treeHash.eq_2]
          show toF one32 = 1
          exact toF_one32 }
      circuit := spend_relation
      wellFormed := ⟨hpre.validZKP, hpre.externalDataBinding, hpre.pubAmtConsistency, hpre.amountRange,
        hpre.encOutLength, hpre.canonicalInputs, hpre.poolNotRecipient, hpre.signerSignature,
        hpre.solMint⟩
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
