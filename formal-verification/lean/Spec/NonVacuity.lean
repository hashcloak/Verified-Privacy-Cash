import Spec.Proofs
import Mathlib.Algebra.Group.PUnit

/-! ## Non-vacuity check (not for review)

The theorems quantify over runs with witnesses (`r.WitnessesFor wit`), and G3a has many
hypotheses. This checks that they can all hold at once, in a toy model of the hash
functions, for any groups and pairing given Groth16 completeness (and, at the end of this
file, for a toy pairing in which Groth16 completeness is proved, `toyComplete`):
- `run_with_witnesses_exists`: a run of one deposit, with a witness for its proof;
- `toy_withdrawal_G3a`: G3a applies to withdrawing that deposit's note: every hypothesis
  of G3a holds;
- `run_with_spend_exists`: a run of two transactions (the deposit, then that withdrawal)
  with witnesses, where the second spends a non-zero note, so the hypotheses of G1a–G1d
  hold for a real spend. -/
namespace LeanSpec.NonVacuity
open LeanSpec

set_option linter.unusedSectionVars false

variable [Groups] [AddCommGroup G1] [Module F G1] [AddCommGroup G2] [Module F G2] [CommGroup GT]
  [Pairing] [Deployment]

/-- Toy hashes. `H2` is constant, so every Merkle path reaches the root `1`; `H3` is linear,
    so the nullifiers below differ. -/
@[reducible] def toyHashes : PoseidonHashes where
  H1 := fun a => a
  H2 := fun _ _ => 1
  H3 := fun a b c => a + 2 * b + 3 * c
  H4 := fun a b c d => a + b + c + d

@[reducible] def toySha : Sha where sha256 := fun _ => []

attribute [local instance] toyHashes toySha

lemma toy_H1 (a : F) : PoseidonHashes.H1 a = a := rfl
lemma toy_H2 (a b : F) : PoseidonHashes.H2 a b = 1 := rfl
lemma toy_H3 (a b c : F) : PoseidonHashes.H3 a b c = a + 2 * b + 3 * c := rfl
lemma toy_H4 (a b c d : F) : PoseidonHashes.H4 a b c d = a + b + c + d := rfl

lemma natCast_ne_zero (n : ℕ) (h0 : 0 < n) (hp : n < p) : ((n : ℕ) : F) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  exact absurd (Nat.le_of_dvd h0 hd) (by omega)

lemma natCast_ne (a b : ℕ) (ha : a < p) (hb : b < p) (hab : a ≠ b) :
    ((a : ℕ) : F) ≠ ((b : ℕ) : F) := by
  intro h
  have := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  exact hab this

lemma one_ne_zero_F : (1 : F) ≠ 0 := by
  have := natCast_ne_zero 1 (by norm_num) (by norm_num [p]); exact_mod_cast this

/-- Every Merkle root in the toy model is `1`. -/
lemma toy_root (cs : List F) (hcap : cs.length < 2^26) : (foldAppend cs initTree).root = 1 := by
  rw [(foldAppend_spec cs hcap).2.1, show (26 : ℕ) = 25 + 1 from rfl, treeHash.eq_2]; rfl

/-- Every opening reaches the root `1` in the toy model. -/
lemma toy_valid (O : Opening) (c : F) : O.Valid c 1 := by
  unfold Opening.Valid
  rw [calcRoot_eq_foldUpTo]
  show stepFn O.index.val (OpeningSib O) (foldUpTo (stepFn O.index.val (OpeningSib O)) 25 c) 25 = 1
  unfold stepFn; split_ifs <;> rfl

def toyCfg : config :=
  { authority := 0, limitAuthority := 0, depositFeeRate := 0, withdrawalFeeRate := 0,
    feeMarginError := 0, maxDepositLimit := 1 }

/-- The pool's account. Signer, recipient and fee recipient are all account `0`. -/
def toyPool : Pubkey := 1

lemma toyPool_ne : (0 : Pubkey) ≠ toyPool := by decide

/-- The pool, freshly initialized; every other account holds 1 lamport, rents are `0`. -/
abbrev toyInit : World :=
  initWorld ⟨toyCfg, fun _ => 1, 0, 0, toyPool, 0, none, rfl, rfl, (fun _ h => by cases h), (by decide)⟩

/-! ### Transaction 0: a deposit of 1 lamport -/

/-- Two zero-amount inputs at leaves 0 and 1; output 0 is a note of 1 lamport owned by the
    secret key `0`. -/
def toyWitness : Witness where
  mint := 0
  inAmt := 0
  inSk := 0
  inR := 0
  openings := fun i => ⟨⟨i.val, by omega⟩, 0⟩
  outAmt := ![1, 0]
  outPk := 0
  outR := 0

def toyInputs (π : Groth16.ProofBytes) : TxInputs where
  R := 1
  pubAmt := 1
  extDataHash := (natOfLE (Sha.sha256 []) : F)
  k0 := 0
  k1 := 11
  outC0 := 1
  outC1 := 0
  extAmt := 1
  f := 0
  s := 0
  A := 0
  t := 0
  encOut0 := []
  encOut1 := []
  π := π
  mintAddr := 0
  pubInputBytes := ![encodeBE32 1, encodeBE32 1, encodeBE32 (natOfLE (Sha.sha256 []) : F),
    encodeBE32 0, encodeBE32 11, encodeBE32 1, encodeBE32 0]

lemma toy_encoded (π : Groth16.ProofBytes) : publicInputsEncoded (toyInputs π) := by
  intro i; fin_cases i <;> exact canonicalEncoding_encodeBE32 _

lemma toy_relation (π : Groth16.ProofBytes) : RelationS (toyInputs π).pubInputs toyWitness where
  outputCommitmentIntegrity := by
    intro j; fin_cases j <;> simp [toyInputs, TxInputs.pubInputs, toyWitness, commit, toy_H4]
  nullifierCorrectness := by
    intro i
    fin_cases i <;>
      (simp [toyInputs, TxInputs.pubInputs, toyWitness, nullifier, Witness.sign, signature,
        Witness.inC, commit, Witness.inPk, toy_H1, toy_H3, toy_H4]; try norm_num)
  noDuplicateNullifiers := by
    simp only [toyInputs, TxInputs.pubInputs, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact fun h => natCast_ne_zero 11 (by norm_num) (by norm_num [p]) (by exact_mod_cast h.symm)
  correctOpenings := by intro i hi; simp [toyWitness] at hi
  amountConservation := by simp [toyInputs, TxInputs.pubInputs, toyWitness]
  outputRangeChecks := by
    haveI : Fact (1 < p) := ⟨by norm_num [p]⟩
    intro j; fin_cases j <;> simp [toyWitness, ZMod.val_one]

noncomputable def depProof (hCompl : Groth16Complete) : Groth16.ProofBytes :=
  Classical.choose (hCompl (toyInputs ⟨[], [], []⟩).pubInputs toyWitness (toy_relation _))

noncomputable abbrev toyDeposit (hCompl : Groth16Complete) : TxInputs := toyInputs (depProof hCompl)

/-- The world after the deposit. -/
noncomputable abbrev W1 (hCompl : Groth16Complete) : World :=
  transactEffects (toyDeposit hCompl) toyInit

lemma toyInit_bal (k : Pubkey) : toyInit.balances k ≤ 1 := by
  simp only [initWorld, Function.update]
  split_ifs <;> simp

lemma toy_delta_le (π : Groth16.ProofBytes) (k : Pubkey) :
    balanceDelta (toyInputs π) toyInit.state.pool toyInit.nullifierRent k ≤ 1 := by
  unfold balanceDelta; split_ifs <;> simp_all [toyInputs, initWorld]

lemma toy_deposit_fit (π : Groth16.ProofBytes) : balancesFit (toyInputs π) toyInit := by
  refine ⟨fun k _ => ?_, fun _ => ?_⟩
  · have h1 : (toyInit.balances k : ℤ) ≤ 1 := by exact_mod_cast toyInit_bal k
    have h2 := toy_delta_le π k
    linarith
  · simp [World.poolBalance, initWorld, toyInputs]

lemma toy_deposit_step (hCompl : Groth16Complete) :
    transact (toyDeposit hCompl) toyInit (W1 hCompl) := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  obtain ⟨π, hdec, hver⟩ := Classical.choose_spec
      (hCompl (toyInputs ⟨[], [], []⟩).pubInputs toyWitness (toy_relation _))
  exact {
    knownRoot := rootBytesKnown_of (toy_encoded _)
      ⟨⟨0, by simp [initWorld, initTree, toyInputs]; rfl⟩, one_ne_zero_F⟩
    canonicalInputs := toy_encoded _
    balancesFit := toy_deposit_fit _
    externalDataBinding := rfl
    minimumFee := by simp [feeSufficient, initWorld, toyCfg, toyInputs]
    pubAmtConsistency := by simp [pubAmtConsistent, toyInputs]
    validZKP := ⟨π, hdec, hver⟩
    newNullifiers := by simp [nullifiersFresh, initWorld]
    distinctNullifiers := fun h => natCast_ne_zero 11 (by norm_num) (by norm_num [p])
      (by simp only [toyInputs] at h; exact_mod_cast h.symm)
    depositLimit := by simp [depositWithinLimit, initWorld, toyCfg, toyInputs]
    poolSolvency := by simp [poolSolvent, toyInputs]
    signerSolvency := by simp [signerSolvent, initWorld, toyInputs, toyPool]
    treeNotFull := by simp [treeHasRoom, initWorld, initTree]
    amountRange := by simp [amountsInRange, toyInputs]
    encOutLength := by simp [encOutsFit, toyInputs]
    poolSeparate := ⟨toyPool_ne, fun _ => toyPool_ne, fun _ => toyPool_ne⟩
  }

/-- The run of the deposit alone. -/
noncomputable def toyRun1 (hCompl : Groth16Complete) : Run toyInit where
  txs := [toyDeposit hCompl]
  ws := fun j => if j = 0 then toyInit else W1 hCompl
  between := fun j => Between.unchanged (if j = 0 then toyInit else W1 hCompl)
  start := rfl
  allowed := fun j _ => Between.Allowed.self _
  step := by
    intro j hj
    simp only [List.length_singleton, Nat.lt_one_iff] at hj
    subst hj
    simpa [World.between_self] using toy_deposit_step hCompl

lemma toyRun1_final (hCompl : Groth16Complete) : (toyRun1 hCompl).final = W1 hCompl := by
  simp [Run.final, toyRun1]

lemma toyRun1_wit (hCompl : Groth16Complete) : (toyRun1 hCompl).WitnessesFor (fun _ => toyWitness) := by
  intro j hj
  simp only [toyRun1, List.length_singleton, Nat.lt_one_iff] at hj
  subst hj
  exact fun _ => toy_relation _

theorem run_with_witnesses_exists (hCompl : Groth16Complete) :
    ∃ (r : Run toyInit) (wit : ℕ → Witness), r.txs.length = 1 ∧ r.WitnessesFor wit :=
  ⟨toyRun1 hCompl, fun _ => toyWitness, rfl, toyRun1_wit hCompl⟩

/-! ### Facts about the world after the deposit -/

lemma W1_tree (hCompl : Groth16Complete) :
    (W1 hCompl).state.tree = foldAppend (leaves (toyRun1 hCompl).txs) initTree := by
  have := ((toyRun1 hCompl).tree 1 le_rfl).1
  simpa [toyRun1] using this

lemma W1_root_mem (hCompl : Groth16Complete) : (1 : F) ∈ Set.range (W1 hCompl).state.tree.history := by
  have hcap : (leaves (toyRun1 hCompl).txs).length < 2^26 := by
    rw [leaves_length]; simp [toyRun1]
  rw [W1_tree, ← toy_root _ hcap]
  exact foldAppend_root_mem_history _

lemma W1_nextIndex (hCompl : Groth16Complete) : (W1 hCompl).state.tree.nextIndex = 2 := by
  rw [W1_tree, foldAppend_nextIndex, leaves_length]; simp [toyRun1]

lemma W1_nullifiers (hCompl : Groth16Complete) : (W1 hCompl).state.nullifiers = {0, 11} := by
  simp [W1, transactEffects, transferEffects_state, initWorld, toyDeposit, toyInputs]

lemma W1_rent (hCompl : Groth16Complete) :
    (W1 hCompl).nullifierRent = 0 ∧ (W1 hCompl).rentExemptMin = 0 := by
  simp only [W1, transactEffects]; unfold transferEffects; split_ifs <;> exact ⟨rfl, rfl⟩

lemma W1_pool (hCompl : Groth16Complete) : (W1 hCompl).state.pool = toyPool := by
  simp [W1, transactEffects, transferEffects_state, initWorld]

lemma W1_poolBalance (hCompl : Groth16Complete) : (W1 hCompl).poolBalance = 1 := by
  have hpre := (toy_deposit_step hCompl).1
  have h := transactEffects_balances (toyDeposit hCompl) toyInit hpre.signerSolvency
    hpre.poolSolvency hpre.poolSeparate toyPool
  have hP : (W1 hCompl).poolBalance = (W1 hCompl).balances toyPool := by
    unfold World.poolBalance; rw [W1_pool]
  rw [hP]
  have hz : (toyInit.balances toyPool : ℤ) = 0 := by simp [initWorld]
  have hd : balanceDelta (toyDeposit hCompl) toyInit.state.pool toyInit.nullifierRent toyPool = 1 := by
    simp [balanceDelta, toyInputs, initWorld, toyPool]
  have : ((W1 hCompl).balances toyPool : ℤ) = 1 := by rw [h, hz, hd]; ring
  exact_mod_cast this

lemma W1_bal (hCompl : Groth16Complete) (k : Pubkey) : ((W1 hCompl).balances k : ℤ) ≤ 2 := by
  have hpre := (toy_deposit_step hCompl).1
  have h := transactEffects_balances (toyDeposit hCompl) toyInit hpre.signerSolvency
    hpre.poolSolvency hpre.poolSeparate k
  have h1 : (toyInit.balances k : ℤ) ≤ 1 := by exact_mod_cast toyInit_bal k
  have h2 := toy_delta_le (depProof hCompl) k
  rw [h]; linarith

/-! ### Transaction 1: withdrawing that note -/

/-- Input 0 spends the deposit's note at leaf 0 (secret key `0`); input 1 is a dummy at
    leaf 1 with the fresh secret key `1`. Both outputs are empty. -/
def wdWitness : Witness where
  mint := 0
  inAmt := ![1, 0]
  inSk := ![0, 1]
  inR := 0
  openings := fun i => ⟨⟨i.val, by omega⟩, 0⟩
  outAmt := 0
  outPk := 0
  outR := 0

def wdInputs (π : Groth16.ProofBytes) : TxInputs where
  R := 1
  pubAmt := -1
  extDataHash := (natOfLE (Sha.sha256 []) : F)
  k0 := 7
  k1 := 21
  outC0 := 0
  outC1 := 0
  extAmt := -1
  f := 0
  s := 0
  A := 0
  t := 0
  encOut0 := []
  encOut1 := []
  π := π
  mintAddr := 0
  pubInputBytes := ![encodeBE32 1, encodeBE32 (-1), encodeBE32 (natOfLE (Sha.sha256 []) : F),
    encodeBE32 7, encodeBE32 21, encodeBE32 0, encodeBE32 0]

lemma wd_encoded (π : Groth16.ProofBytes) : publicInputsEncoded (wdInputs π) := by
  intro i; fin_cases i <;> exact canonicalEncoding_encodeBE32 _

lemma wd_nullifiers (π : Groth16.ProofBytes) (i : Fin 2) : (wdInputs π).pubInputs.nullifiers i
    = nullifier (wdWitness.inC i) (wdWitness.sign i) (wdWitness.openings i).index := by
  fin_cases i <;>
    simp [wdInputs, TxInputs.pubInputs, wdWitness, nullifier, Witness.sign, signature,
      Witness.inC, commit, Witness.inPk, toy_H1, toy_H3, toy_H4] <;> norm_num

lemma wd_fit (hCompl : Groth16Complete) (π : Groth16.ProofBytes) :
    balancesFit (wdInputs π) (W1 hCompl) := by
  refine ⟨fun k _ => ?_, fun h => by simp [wdInputs] at h⟩
  have h1 := W1_bal hCompl k
  have h2 : balanceDelta (wdInputs π) (W1 hCompl).state.pool (W1 hCompl).nullifierRent k ≤ 1 := by
    rw [(W1_rent hCompl).1]
    unfold balanceDelta; split_ifs <;> simp_all [wdInputs]
  linarith

lemma ne_7_21 : (7 : F) ≠ 21 := by
  have := natCast_ne 7 21 (by norm_num [p]) (by norm_num [p]) (by norm_num); exact_mod_cast this

lemma wd_fresh (hCompl : Groth16Complete) (π : Groth16.ProofBytes) (i : Fin 2) :
    (wdInputs π).pubInputs.nullifiers i ∉ (W1 hCompl).state.nullifiers := by
  rw [W1_nullifiers]
  have h70 : (7 : F) ≠ 0 := by have := natCast_ne_zero 7 (by norm_num) (by norm_num [p]); exact_mod_cast this
  have h710 : (7 : F) ≠ 11 := by
    have := natCast_ne 7 11 (by norm_num [p]) (by norm_num [p]) (by norm_num); exact_mod_cast this
  have h210 : (21 : F) ≠ 0 := by have := natCast_ne_zero 21 (by norm_num) (by norm_num [p]); exact_mod_cast this
  have h2110 : (21 : F) ≠ 11 := by
    have := natCast_ne 21 11 (by norm_num [p]) (by norm_num [p]) (by norm_num); exact_mod_cast this
  fin_cases i <;> simp [wdInputs, TxInputs.pubInputs, h70, h710, h210, h2110]

/-- **The hypotheses of G3a can all hold.** After `toyRun1`, withdrawing the deposit's note (a
    real, non-zero spend) against the current root (`k = 2`) satisfies every hypothesis of G3a. -/
theorem toy_G3a_hypotheses (hCompl : Groth16Complete) :
    ∃ (inputs : TxInputs) (witness : Witness) (k : ℕ),
      witness.inAmt 0 ≠ 0
      ∧ (toyRun1 hCompl).WitnessesFor (fun _ => toyWitness)
      ∧ RootInWindow (toyRun1 hCompl) inputs.R k
      ∧ OwnsUnspentNotes (toyRun1 hCompl) (fun _ => toyWitness) witness k
      ∧ BuiltHonestly (toyRun1 hCompl).final inputs witness
      ∧ PolicyChecksPass (toyRun1 hCompl).final inputs := by
  have hcap2 : ((leaves (toyRun1 hCompl).txs).take 2).length < 2^26 := by
    rw [List.length_take, leaves_length]; simp [toyRun1]
  have hfin := toyRun1_final hCompl
  have hunsp0 : (0 : ℕ) ∈ (toyRun1 hCompl).unspent (fun _ => toyWitness) := by
    simp [Run.unspent, toyRun1, toyWitness]
  refine ⟨wdInputs ⟨[], [], []⟩, wdWitness, 2, ?_, toyRun1_wit hCompl, ?_, ?_, ?_, ?_⟩
  · show wdWitness.inAmt 0 ≠ 0
    simp only [wdWitness, Matrix.cons_val_zero]
    exact one_ne_zero_F
  · exact { isPrefix := by simp [toyRun1]
            isPrefixRoot := by rw [toy_root _ hcap2]; rfl
            inWindow := by rw [hfin]; exact W1_root_mem hCompl }
  · refine { unspent := ?_, inTree := ?_, isOwnersNote := ?_, different := ?_, freshDummyKeys := ?_ }
    · intro i hne; fin_cases i
      · simpa [wdWitness] using hunsp0
      · simp [wdWitness] at hne
    · intro i hne; fin_cases i
      · simp [wdWitness]
      · simp [wdWitness] at hne
    · intro i hne; fin_cases i
      · simp [Witness.inNote, leafNote, Witness.outNote, wdWitness, toyWitness, Witness.inPk, toy_H1]
      · simp [wdWitness] at hne
    · -- input 1 has zero amount
      intro _ h1; simp [wdWitness] at h1
    · -- the dummy input's key `1` is used by no input of the run
      intro i hz j hj i'
      fin_cases i
      · simp [wdWitness] at hz; exact absurd hz one_ne_zero_F
      · simp only [toyWitness, wdWitness]
        have := natCast_ne_zero 1 (by norm_num) (by norm_num [p])
        intro h; apply this; simp only [Nat.cast_one]
        have h' : (0 : F) = 1 := h
        exact h'.symm
  · refine { outputs := ?_, nullifiers := wd_nullifiers _, amounts := ?_,
             outputRange := ?_, externalData := rfl, publicAmount := ?_, distinctNullifiers := ne_7_21,
             amountRange := ?_, encOutLength := ?_, poolSeparate := ?_, signerCanPay := ?_,
             encodings := wd_encoded _ }
    · intro j; fin_cases j <;> simp [wdInputs, TxInputs.pubInputs, wdWitness, commit, toy_H4]
    · simp [wdInputs, TxInputs.pubInputs, wdWitness]
    · intro j; simp [wdWitness]
    · simp [pubAmtConsistent, wdInputs]
    · simp [amountsInRange, wdInputs]
    · simp [encOutsFit, wdInputs]
    · rw [hfin, W1_pool]; exact ⟨toyPool_ne, fun _ => toyPool_ne, fun _ => toyPool_ne⟩
    · rw [hfin]; unfold signerSolvent; rw [(W1_rent hCompl).1]; simp [wdInputs]
  · refine { fee := ?_, depositLimit := ?_, depositFee := ?_, treeRoom := ?_,
             balancesFit := by rw [hfin]; exact wd_fit hCompl _ }
    · rw [hfin]; simp [feeSufficient, W1, transactEffects, transferEffects_state, initWorld, toyCfg, wdInputs]
    · simp [depositWithinLimit, wdInputs]
    · simp [wdInputs]
    · rw [hfin]; unfold treeHasRoom; rw [W1_nextIndex]; norm_num

/-! ### The run of both transactions -/

lemma wd_relation (π : Groth16.ProofBytes) : RelationS (wdInputs π).pubInputs wdWitness where
  outputCommitmentIntegrity := by
    intro j; fin_cases j <;> simp [wdInputs, TxInputs.pubInputs, wdWitness, commit, toy_H4]
  nullifierCorrectness := wd_nullifiers π
  noDuplicateNullifiers := by
    simp only [wdInputs, TxInputs.pubInputs, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ne_7_21
  correctOpenings := fun i _ => toy_valid _ _
  amountConservation := by simp [wdInputs, TxInputs.pubInputs, wdWitness]
  outputRangeChecks := by intro j; simp [wdWitness]

noncomputable def wdProof (hCompl : Groth16Complete) : Groth16.ProofBytes :=
  Classical.choose (hCompl (wdInputs ⟨[], [], []⟩).pubInputs wdWitness (wd_relation _))

noncomputable abbrev toyWithdrawal (hCompl : Groth16Complete) : TxInputs := wdInputs (wdProof hCompl)

lemma toy_withdrawal_step (hCompl : Groth16Complete) :
    transact (toyWithdrawal hCompl) (W1 hCompl) (transactEffects (toyWithdrawal hCompl) (W1 hCompl)) := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  have hcfg : (W1 hCompl).state.config = toyCfg := by
    simp [W1, transactEffects, transferEffects_state, initWorld]
  have hrent : (W1 hCompl).rentExemptMin = 0 := (W1_rent hCompl).2
  obtain ⟨π, hdec, hver⟩ := Classical.choose_spec
      (hCompl (wdInputs ⟨[], [], []⟩).pubInputs wdWitness (wd_relation _))
  exact {
    knownRoot := rootBytesKnown_of (wd_encoded _) ⟨W1_root_mem hCompl, one_ne_zero_F⟩
    canonicalInputs := wd_encoded _
    balancesFit := wd_fit hCompl _
    externalDataBinding := rfl
    minimumFee := by rw [hcfg]; simp [feeSufficient, toyCfg, wdInputs]
    pubAmtConsistency := by simp [pubAmtConsistent, wdInputs]
    validZKP := ⟨π, hdec, hver⟩
    newNullifiers := ⟨wd_fresh hCompl (wdProof hCompl) 0, wd_fresh hCompl (wdProof hCompl) 1⟩
    distinctNullifiers := ne_7_21
    depositLimit := by simp [depositWithinLimit, wdInputs]
    poolSolvency := by
      refine ⟨fun _ => ?_, fun h => by simp [wdInputs] at h⟩
      rw [W1_poolBalance, hrent]; simp [wdInputs]
    signerSolvency := by unfold signerSolvent; rw [(W1_rent hCompl).1]; simp [wdInputs]
    treeNotFull := by unfold treeHasRoom; rw [W1_nextIndex]; norm_num
    amountRange := by simp [amountsInRange, wdInputs]
    encOutLength := by simp [encOutsFit, wdInputs]
    poolSeparate := by rw [W1_pool]; exact ⟨toyPool_ne, fun _ => toyPool_ne, fun _ => toyPool_ne⟩
  }

/-- The run of the deposit followed by the withdrawal. -/
noncomputable def toyRun2 (hCompl : Groth16Complete) : Run toyInit where
  txs := [toyDeposit hCompl, toyWithdrawal hCompl]
  ws := fun j => if j = 0 then toyInit else if j = 1 then W1 hCompl
    else transactEffects (toyWithdrawal hCompl) (W1 hCompl)
  between := fun j => Between.unchanged (if j = 0 then toyInit else if j = 1 then W1 hCompl
    else transactEffects (toyWithdrawal hCompl) (W1 hCompl))
  start := rfl
  allowed := fun j _ => Between.Allowed.self _
  step := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simpa [World.between_self] using toy_deposit_step hCompl
    · simpa [World.between_self] using toy_withdrawal_step hCompl

theorem run_with_spend_exists (hCompl : Groth16Complete) :
    ∃ (r : Run toyInit) (wit : ℕ → Witness),
      r.txs.length = 2 ∧ r.WitnessesFor wit ∧ (wit 1).inAmt 0 ≠ 0 := by
  refine ⟨toyRun2 hCompl, fun j => if j = 0 then toyWitness else wdWitness, rfl, ?_, ?_⟩
  · intro j hj
    simp only [toyRun2, List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact fun _ => toy_relation _
    · exact fun _ => wd_relation _
  · show wdWitness.inAmt 0 ≠ 0
    simp only [wdWitness, Matrix.cons_val_zero]
    exact one_ne_zero_F


/-- **The toy withdrawal is accepted.** After `toyRun1`, the program accepts the withdrawal of
    the deposit's note. -/
theorem toy_withdrawal_accepted (hCompl : Groth16Complete) :
    CanBeAccepted (wdInputs ⟨[], [], []⟩) (toyRun1 hCompl).final := by
  refine ⟨wdProof hCompl, ?_⟩
  rw [toyRun1_final]
  exact toy_withdrawal_step hCompl

end LeanSpec.NonVacuity

/-! ### A toy pairing, so that Groth16 completeness holds

Everything above holds for any groups and pairing, given Groth16 completeness. Here the groups
and the pairing are a deliberately broken toy, like the hashes: `G1 = G2 = F`, `GT = Unit`,
every pairing is `1`, every byte string decodes (to `0`), and the key is all zeros. Every
proof then verifies, so `Groth16Complete` holds (`toyComplete`). This shows the hypotheses can
hold together; it says nothing about real cryptography. -/
namespace LeanSpec.NonVacuity
open LeanSpec

/-- Toy groups: `G1 = G2 = F`, `GT = Unit`; every byte string decodes to the point `0`. -/
@[reducible] def toyGroups : Groups := ⟨F, F, Unit, fun _ => some 0, fun _ => some 0⟩

attribute [local instance] toyGroups

-- The toy groups' structure: that of `F` and of `Unit`.
@[reducible] def toyG1Group : AddCommGroup G1 := inferInstanceAs (AddCommGroup F)
@[reducible] def toyG2Group : AddCommGroup G2 := inferInstanceAs (AddCommGroup F)
attribute [local instance] toyG1Group toyG2Group
@[reducible] def toyG1Module : Module F G1 := inferInstanceAs (Module F F)
@[reducible] def toyG2Module : Module F G2 := inferInstanceAs (Module F F)
@[reducible] def toyGTGroup : CommGroup GT := inferInstanceAs (CommGroup Unit)
attribute [local instance] toyG1Module toyG2Module toyGTGroup

/-- Toy pairing: always `1` (`GT = Unit` has no other element). Bilinear, trivially. -/
@[reducible] def toyPairing : Pairing := ⟨fun _ _ => 1, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- Toy key: all points `0`. -/
@[reducible] def toyDeployment : Deployment := ⟨⟨0, 0, 0, 0, fun _ => 0⟩⟩

attribute [local instance] toyPairing toyDeployment

/-- In the toy groups every proof verifies, so Groth16 completeness holds (for any hashes). -/
theorem toyComplete [PoseidonHashes] : Groth16Complete :=
  fun _ _ _ => ⟨⟨[], [], []⟩, ⟨0, 0, 0⟩, rfl, rfl⟩

end LeanSpec.NonVacuity
