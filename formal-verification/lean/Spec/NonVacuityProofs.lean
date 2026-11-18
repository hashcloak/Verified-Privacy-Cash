import Spec.Proofs
import Spec.NonVacuitySetting

/-! ## Non-vacuity proofs (not for review)

The proofs of the statements in `Spec/NonVacuityStatements.lean`, in the toy setting of
`Spec/NonVacuitySetting.lean`. They work for any groups and pairing given Groth16 completeness
on the wire (`Groth16CompleteBytes`), proved at the end of this file for the toy pairing
(`toyCompleteBytes`):
- `run_with_witnesses_exists`: a run of one deposit, with a witness for its proof;
- `run_with_spend_exists`: a run of two transactions (the deposit, then a withdrawal of its
  note) with witnesses, where the second spends the deposit's non-zero note, so the
  hypotheses of G1a–G1d hold for a real spend;
- `toy_G3_hypotheses`: every hypothesis of G3a holds for that withdrawal after the deposit, and
  it is accepted;
- `toy_G3b_hypotheses`: every hypothesis of G3b's `WayIsAccepted` holds for that withdrawal with
  any split of the note between recipient and fee, so for whichever split G3b picks;
- `toy_G4_hypotheses`, `toy_G2a_hypotheses`, `toy_G2b_hypotheses`: likewise for G4a/G4b, G2a
  and G2b. -/
namespace LeanSpec.NonVacuity
open LeanSpec

set_option linter.unusedSectionVars false

variable [Groups] [AddCommGroup G1] [Module F G1] [AddCommGroup G2] [Module F G2] [CommGroup GT]
  [Pairing] [Deployment]

/-- Groth16 completeness on the wire: every statement with a witness has a proof, sent as bytes,
    whose points decode and which verifies. The toy run takes its proofs from this. -/
def Groth16CompleteBytes [PoseidonHashes] [Sha] : Prop :=
  ∀ x w, RelationS x w → ∃ πb : Groth16.ProofBytes, ∃ π,
    πb.decode = some π ∧ Groth16.verify Deployment.vk π x

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
  { authority := 0, limitAuthority := 0, depositFeeRate := 0, withdrawalFeeRate := 25,
    feeErrorMargin := 500, maxDepositLimit := 1_000_000_000_000 }

/-- The pool's account. Signer, recipient and fee recipient are all account `0`. -/
def toyPool : Pubkey := 1

lemma toyPool_ne : (0 : Pubkey) ≠ toyPool := by decide

/-- The tree's and the config's accounts: two addresses above every toy nullifier address. -/
def toyTree : Pubkey := BitVec.ofNat 256 (2^255)
def toyConfig : Pubkey := BitVec.ofNat 256 (2^255 + 1)

/-- The addresses of nullifier accounts: `2·v + 2` for input 0 and `2·v + 3` for input 1, where
    `v` is the bytes' big-endian value. Never `0` (the signer) or `1` (the pool), and different
    for different inputs or values. -/
def toyAddr (i : Fin 2) (b : Bytes) : Pubkey := BitVec.ofNat 256 (2 * natOfBE b + 2 + i.val)

lemma natOfBE_encodeBE32 (x : F) : natOfBE (encodeBE32 x) = x.val := by
  obtain ⟨-, hlt, hx⟩ := canonicalEncoding_encodeBE32 x
  have := ZMod.val_natCast_of_lt hlt
  rw [hx] at this
  exact this.symm

lemma toyAddr_toNat (i : Fin 2) (x : F) :
    (toyAddr i (encodeBE32 x)).toNat = 2 * x.val + 2 + i.val := by
  have hx := ZMod.val_lt x
  have hp : p < 28948022309329048855892746252171976963317496166410141009864396001978282409984 := by
    norm_num [p]
  have h256 : (2 : ℕ)^256
      = 115792089237316195423570985008687907853269984665640564039457584007913129639936 := by
    norm_num
  have hi := i.isLt
  rw [toyAddr, natOfBE_encodeBE32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by rw [h256]; omega)]

lemma toyAddr_ne {i j : Fin 2} {x y : F} (h : i ≠ j ∨ x ≠ y) :
    toyAddr i (encodeBE32 x) ≠ toyAddr j (encodeBE32 y) := by
  haveI : NeZero p := ⟨by norm_num [p]⟩
  intro he
  have := congrArg BitVec.toNat he
  rw [toyAddr_toNat, toyAddr_toNat] at this
  have hi := i.isLt
  have hj := j.isLt
  rcases h with h | h
  · exact h (Fin.ext (by omega))
  · exact h (ZMod.val_injective _ (by omega))

lemma toyAddr_ne_small (i : Fin 2) (x : F) (n : ℕ) (hn : n < 2) :
    toyAddr i (encodeBE32 x) ≠ BitVec.ofNat 256 n := by
  intro he
  have := congrArg BitVec.toNat he
  rw [toyAddr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans hn (by norm_num))] at this
  omega

/-- A toy nullifier address is below every address from `2p + 4` on. -/
lemma toyAddr_ne_big (i : Fin 2) (x : F) (n : ℕ) (hn : 2 * p + 4 ≤ n) (hn' : n < 2^256) :
    toyAddr i (encodeBE32 x) ≠ BitVec.ofNat 256 n := by
  intro he
  have := congrArg BitVec.toNat he
  rw [toyAddr_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn'] at this
  have hx := ZMod.val_lt x
  have hi := i.isLt
  omega

/-- The toy worlds' program accounts are the pool and their nullifier accounts; a toy nullifier
    address is not the pool. -/
lemma toyAddr_notProgram (st : State) (hp : st.pool = toyPool) (ht : st.treeAccount = toyTree)
    (hc : st.configAccount = toyConfig) (i : Fin 2) (x : F)
    (hn : toyAddr i (encodeBE32 x) ∉ st.nullifierAccounts) :
    ¬ st.IsProgramAccount (toyAddr i (encodeBE32 x)) := by
  rintro (h | h | h | h)
  · rw [hp] at h; exact toyAddr_ne_small i x 1 (by norm_num) h
  · exact hn h
  · rw [ht] at h; exact toyAddr_ne_big i x (2^255) (by norm_num [p]) (by norm_num) h
  · rw [hc] at h; exact toyAddr_ne_big i x (2^255 + 1) (by norm_num [p]) (by norm_num) h

/-- The toy signer, account `0`, is none of the program's accounts. -/
lemma zero_notProgram (st : State) (hp : st.pool = toyPool) (ht : st.treeAccount = toyTree)
    (hc : st.configAccount = toyConfig) (hn : (0 : Pubkey) ∉ st.nullifierAccounts) :
    ¬ st.IsProgramAccount 0 := by
  rintro (h | h | h | h)
  · rw [hp] at h; exact toyPool_ne h
  · exact hn h
  · rw [ht] at h; exact absurd h (by decide)
  · rw [hc] at h; exact absurd h (by decide)

/-- The pool's parameters: every other account holds 2 lamports, rents are `0`. -/
abbrev toyParams : InitParams where
  cfg := toyCfg
  balances := fun _ => 2
  rentExemptMin := 0
  nullifierRent := 0
  pool := toyPool
  nullifierAddr := toyAddr
  treeAccount := toyTree
  configAccount := toyConfig
  treeRent := 0
  configRent := 0
  balances_fit := fun _ => by norm_num
  initializer := 0
  initializer_not_created := by decide
  signers := [0]
  initializer_signed := by simp
  admin := none
  authority_init := rfl
  limitAuthority_init := rfl
  admin_init := fun _ h => by cases h
  depositFeeRate_default := rfl
  withdrawalFeeRate_default := rfl
  feeErrorMargin_default := rfl
  maxDepositLimit_default := rfl

/-- The pool, freshly initialized. -/
abbrev toyInit : World := initWorld toyParams

/-! ### Transaction 0: a deposit of 2 lamports -/

/-- Two zero-amount inputs at leaves 0 and 1; output 0 is a note of 2 lamports owned by the
    secret key `0`. -/
def toyWitness : Witness where
  mint := 0
  inAmt := 0
  inSk := 0
  inR := 0
  openings := fun i => ⟨⟨i.val, by omega⟩, 0⟩
  outAmt := ![2, 0]
  outPk := 0
  outR := 0

def toyInputs (π : Groth16.ProofBytes) : TxInputs where
  R := 1
  pubAmt := 2
  extDataHash := (natOfLE (Sha.sha256 []) : F)
  k0 := 0
  k1 := 11
  outC0 := 2
  outC1 := 0
  extAmt := 2
  f := 0
  s := 0
  signers := [0]
  A := 0
  t := 0
  encOut0 := []
  encOut1 := []
  π := π
  mintAddr := Deployment.solMint
  pubInputBytes := ![encodeBE32 1, encodeBE32 2, encodeBE32 (natOfLE (Sha.sha256 []) : F),
    encodeBE32 0, encodeBE32 11, encodeBE32 2, encodeBE32 0]

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
    have hval : ZMod.val (2 : F) = 2 := by
      have := ZMod.val_natCast_of_lt (n := p) (a := 2) (by norm_num [p]); exact_mod_cast this
    intro j; fin_cases j <;> simp [toyWitness, hval]

noncomputable def depProof (hCompl : Groth16CompleteBytes) : Groth16.ProofBytes :=
  Classical.choose (hCompl (toyInputs ⟨[], [], []⟩).pubInputs toyWitness (toy_relation _))

noncomputable abbrev toyDeposit (hCompl : Groth16CompleteBytes) : TxInputs := toyInputs (depProof hCompl)

/-- The world after the deposit. -/
noncomputable abbrev W1 (hCompl : Groth16CompleteBytes) : World :=
  transactEffects (toyDeposit hCompl) toyInit

lemma toyInit_bal (k : Pubkey) : toyInit.balances k ≤ 2 := by
  simp only [initWorld, Function.update]
  split_ifs <;> simp

lemma toyInit_fit (k : Pubkey) : toyInit.balances k < 2 ^ 64 := lt_of_le_of_lt (toyInit_bal k) (by norm_num)

/-- With a nullifier rent of `0`, nothing is topped up. -/
lemma topUp_zero (w : World) (h : w.nullifierRent = 0) (inputs : TxInputs) (i : Fin 2) :
    w.nullifierTopUp inputs i = 0 := by
  unfold World.nullifierTopUp; rw [h]; exact Nat.zero_sub _

/-- The deposit's nullifier accounts: for `0` (input 0) and `11` (input 1). -/
lemma toy_dep_acct0 (π : Groth16.ProofBytes) :
    toyInit.state.newNullifierAccount (toyInputs π) 0 = toyAddr 0 (encodeBE32 0) := rfl
lemma toy_dep_acct1 (π : Groth16.ProofBytes) :
    toyInit.state.newNullifierAccount (toyInputs π) 1 = toyAddr 1 (encodeBE32 11) := rfl

lemma toy_delta_le (π : Groth16.ProofBytes) (k : Pubkey) :
    balanceDelta (toyInputs π) toyInit k ≤ 2 := by
  unfold balanceDelta
  simp only [topUp_zero toyInit rfl, Nat.cast_zero, add_zero, ite_self, sub_zero]
  split_ifs <;> simp_all [toyInputs, initWorld]

lemma toy_deposit_fit (π : Groth16.ProofBytes) : balancesFit (toyInputs π) toyInit := by
  refine ⟨fun k _ => ?_, fun _ => ?_⟩
  · have h1 : (toyInit.balances k : ℤ) ≤ 2 := by exact_mod_cast toyInit_bal k
    have h2 := toy_delta_le π k
    linarith
  · simp [World.poolBalance, initWorld, toyInputs]

lemma toy_deposit_step (hCompl : Groth16CompleteBytes) :
    transact (toyDeposit hCompl) toyInit (W1 hCompl) := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
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
    newNullifiers := by simp [nullifiersFresh, State.spent, initWorld]
    distinctNullifiers := fun h => natCast_ne_zero 11 (by norm_num) (by norm_num [p])
      (by simp only [toyInputs] at h; exact_mod_cast h.symm)
    nullifierAccountsNew := by
      refine ⟨?_, ?_, ?_⟩
      · rw [toy_dep_acct0, toy_dep_acct1]; exact toyAddr_ne (Or.inl (by decide))
      · rw [toy_dep_acct0]; exact toyAddr_notProgram _ rfl rfl rfl _ _ (by simp [initWorld])
      · rw [toy_dep_acct1]; exact toyAddr_notProgram _ rfl rfl rfl _ _ (by simp [initWorld])
    depositLimit := by simp [depositWithinLimit, initWorld, toyCfg, toyInputs]
    poolSolvency := by simp [poolSolvent, toyInputs]
    signerSolvency := by
      unfold signerSolvent; rw [topUp_zero toyInit rfl, topUp_zero toyInit rfl]
      simp [initWorld, toyInputs, toyPool, Function.update, toyTree, toyConfig]
    treeNotFull := by simp [treeHasRoom, initWorld, initTree]
    amountRange := by simp [amountsInRange, toyInputs]
    encOutLength := by simp [encOutsFit, toyInputs]
    poolNotRecipient := ⟨fun _ => toyPool_ne, fun _ => toyPool_ne⟩
    signerSignature := by simp [signerSigned, toyInputs]
    solMint := rfl
    signerNotPoolNotNullifiers := by
      refine ⟨zero_notProgram _ rfl rfl rfl (by simp [initWorld]), ?_, ?_⟩
      · rw [toy_dep_acct0]; exact (toyAddr_ne_small 0 0 0 (by norm_num)).symm
      · rw [toy_dep_acct1]; exact (toyAddr_ne_small 1 11 0 (by norm_num)).symm
  }

/-- The run of the deposit alone. -/
noncomputable def toyRun1 (hCompl : Groth16CompleteBytes) : Run toyInit where
  txs := [toyDeposit hCompl]
  ws := fun j => if j = 0 then toyInit else W1 hCompl
  updatedValues := fun j =>
    UpdatedValuesBetweenTransacts.unchanged (if j = 0 then toyInit else W1 hCompl)
  start := rfl
  allowed := fun j hj => by
    obtain rfl : j = 0 := by simpa using hj
    exact UpdatedValuesBetweenTransacts.Allowed.self _ toyInit_fit
  step := by
    intro j hj
    simp only [List.length_singleton, Nat.lt_one_iff] at hj
    subst hj
    simpa [World.withUpdatedValues_self] using toy_deposit_step hCompl

lemma toyRun1_final (hCompl : Groth16CompleteBytes) : (toyRun1 hCompl).final = W1 hCompl := by
  simp [Run.final, toyRun1]

lemma toyRun1_wit (hCompl : Groth16CompleteBytes) : (toyRun1 hCompl).WitnessesFor (fun _ => toyWitness) := by
  intro j hj
  simp only [toyRun1, List.length_singleton, Nat.lt_one_iff] at hj
  subst hj
  exact fun _ => toy_relation _

theorem run_with_witnesses_exists (hCompl : Groth16CompleteBytes) :
    ∃ (r : Run toyInit) (wit : ℕ → Witness), r.txs.length = 1 ∧ r.WitnessesFor wit :=
  ⟨toyRun1 hCompl, fun _ => toyWitness, rfl, toyRun1_wit hCompl⟩

/-! ### Facts about the world after the deposit -/

lemma W1_tree (hCompl : Groth16CompleteBytes) :
    (W1 hCompl).state.tree = foldAppend (leaves (toyRun1 hCompl).txs) initTree := by
  have := ((toyRun1 hCompl).tree 1 le_rfl).1
  simpa [toyRun1] using this

lemma W1_root_mem (hCompl : Groth16CompleteBytes) : (1 : F) ∈ Set.range (W1 hCompl).state.tree.history := by
  have hcap : (leaves (toyRun1 hCompl).txs).length < 2^26 := by
    rw [leaves_length]; simp [toyRun1]
  rw [W1_tree, ← toy_root _ hcap]
  exact foldAppend_root_mem_history _

lemma W1_nextIndex (hCompl : Groth16CompleteBytes) : (W1 hCompl).state.tree.nextIndex = 2 := by
  rw [W1_tree, foldAppend_nextIndex, leaves_length]; simp [toyRun1]

lemma W1_accounts (hCompl : Groth16CompleteBytes) : (W1 hCompl).state.nullifierAccounts
    = {toyAddr 0 (encodeBE32 0), toyAddr 1 (encodeBE32 11)} := by
  show (transferEffects _ (nullifierRentEffects _ _)).state.nullifierAccounts ∪ _ = _
  rw [transferEffects_state, nullifierRentEffects_state, toy_dep_acct0, toy_dep_acct1]
  simp [initWorld]

lemma W1_addr (hCompl : Groth16CompleteBytes) : (W1 hCompl).state.nullifierAddr = toyAddr := by
  show (transferEffects _ (nullifierRentEffects _ _)).state.nullifierAddr = _
  rw [transferEffects_state, nullifierRentEffects_state]; rfl

lemma W1_rent (hCompl : Groth16CompleteBytes) :
    (W1 hCompl).nullifierRent = 0 ∧ (W1 hCompl).rentExemptMin = 0 := by
  simp only [W1, transactEffects]; unfold transferEffects; split_ifs <;> exact ⟨rfl, rfl⟩

lemma W1_pool (hCompl : Groth16CompleteBytes) : (W1 hCompl).state.pool = toyPool := by
  simp [W1, transactEffects, transferEffects_state, initWorld]

lemma W1_poolBalance (hCompl : Groth16CompleteBytes) : (W1 hCompl).poolBalance = 2 := by
  have hpre := (toy_deposit_step hCompl).1
  have h := transactEffects_balances (toyDeposit hCompl) toyInit hpre.signerSolvency
    hpre.poolSolvency hpre.poolNotRecipient hpre.signerNotPoolNotNullifiers hpre.nullifierAccountsNew toyPool
  have hP : (W1 hCompl).poolBalance = (W1 hCompl).balances toyPool := by
    unfold World.poolBalance; rw [W1_pool]
  rw [hP]
  have hz : (toyInit.balances toyPool : ℤ) = 0 := by simp [initWorld]
  have hd : balanceDelta (toyDeposit hCompl) toyInit toyPool = 2 := by
    simp [balanceDelta, toyInputs, initWorld, toyPool]
  have : ((W1 hCompl).balances toyPool : ℤ) = 2 := by rw [h, hz, hd]; ring
  exact_mod_cast this

lemma W1_bal (hCompl : Groth16CompleteBytes) (k : Pubkey) : ((W1 hCompl).balances k : ℤ) ≤ 4 := by
  have hpre := (toy_deposit_step hCompl).1
  have h := transactEffects_balances (toyDeposit hCompl) toyInit hpre.signerSolvency
    hpre.poolSolvency hpre.poolNotRecipient hpre.signerNotPoolNotNullifiers hpre.nullifierAccountsNew k
  have h1 : (toyInit.balances k : ℤ) ≤ 2 := by exact_mod_cast toyInit_bal k
  have h2 := toy_delta_le (depProof hCompl) k
  rw [h]; linarith

/-! ### Transaction 1: withdrawing that note, 1 lamport to the recipient and 1 as the fee -/

/-- Input 0 spends the deposit's note at leaf 0 (secret key `0`); input 1 is a dummy at
    leaf 1 with the fresh secret key `1`. Both outputs are empty. -/
def wdWitness : Witness where
  mint := 0
  inAmt := ![2, 0]
  inSk := ![0, 1]
  inR := 0
  openings := fun i => ⟨⟨i.val, by omega⟩, 0⟩
  outAmt := 0
  outPk := 0
  outR := 0

def wdInputs (π : Groth16.ProofBytes) : TxInputs where
  R := 1
  pubAmt := -2
  extDataHash := (natOfLE (Sha.sha256 []) : F)
  k0 := 14
  k1 := 21
  outC0 := 0
  outC1 := 0
  extAmt := -1
  f := 1
  s := 0
  signers := [0]
  A := 0
  t := 0
  encOut0 := []
  encOut1 := []
  π := π
  mintAddr := Deployment.solMint
  pubInputBytes := ![encodeBE32 1, encodeBE32 (-2), encodeBE32 (natOfLE (Sha.sha256 []) : F),
    encodeBE32 14, encodeBE32 21, encodeBE32 0, encodeBE32 0]

lemma wd_encoded (π : Groth16.ProofBytes) : publicInputsEncoded (wdInputs π) := by
  intro i; fin_cases i <;> exact canonicalEncoding_encodeBE32 _

lemma wd_nullifiers (π : Groth16.ProofBytes) (i : Fin 2) : (wdInputs π).pubInputs.nullifiers i
    = nullifier (wdWitness.inC i) (wdWitness.sign i) (wdWitness.openings i).index := by
  fin_cases i <;>
    simp [wdInputs, TxInputs.pubInputs, wdWitness, nullifier, Witness.sign, signature,
      Witness.inC, commit, Witness.inPk, toy_H1, toy_H3, toy_H4] <;> norm_num

lemma wd_fit (hCompl : Groth16CompleteBytes) (π : Groth16.ProofBytes) :
    balancesFit (wdInputs π) (W1 hCompl) := by
  refine ⟨fun k _ => ?_, fun h => by simp [wdInputs] at h⟩
  have h1 := W1_bal hCompl k
  have h2 : balanceDelta (wdInputs π) (W1 hCompl) k ≤ 2 := by
    unfold balanceDelta
    simp only [topUp_zero (W1 hCompl) (W1_rent hCompl).1, Nat.cast_zero, add_zero, ite_self,
      sub_zero]
    split_ifs <;> simp_all [wdInputs]
  linarith

lemma ne_14_21 : (14 : F) ≠ 21 := by
  have := natCast_ne 14 21 (by norm_num [p]) (by norm_num [p]) (by norm_num); exact_mod_cast this

/-- The withdrawal's nullifier accounts: for `14` (input 0) and `21` (input 1). -/
lemma wd_acct (hCompl : Groth16CompleteBytes) (π : Groth16.ProofBytes) (slot i : Fin 2) :
    (W1 hCompl).state.nullifierAddr slot ((wdInputs π).nullifierBytes i)
      = toyAddr slot (encodeBE32 (![14, 21] i)) := by
  rw [W1_addr]; fin_cases i <;> rfl

lemma wd_fresh (hCompl : Groth16CompleteBytes) (π : Groth16.ProofBytes) (i : Fin 2) :
    ¬ (W1 hCompl).state.spent ((wdInputs π).nullifierBytes i) := by
  have h70 : (14 : F) ≠ 0 := by have := natCast_ne_zero 14 (by norm_num) (by norm_num [p]); exact_mod_cast this
  have h710 : (14 : F) ≠ 11 := by
    have := natCast_ne 14 11 (by norm_num [p]) (by norm_num [p]) (by norm_num); exact_mod_cast this
  have h210 : (21 : F) ≠ 0 := by have := natCast_ne_zero 21 (by norm_num) (by norm_num [p]); exact_mod_cast this
  have h2110 : (21 : F) ≠ 11 := by
    have := natCast_ne 21 11 (by norm_num [p]) (by norm_num [p]) (by norm_num); exact_mod_cast this
  unfold State.spent
  rw [wd_acct, wd_acct, W1_accounts]
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
      Finset.mem_insert, Finset.mem_singleton, not_or] <;>
    exact ⟨⟨toyAddr_ne (Or.inr (by assumption)), toyAddr_ne (Or.inl h01)⟩,
      ⟨toyAddr_ne (Or.inl h01.symm), toyAddr_ne (Or.inr (by assumption))⟩⟩

/-- The withdrawal's new nullifier accounts are not the pool, not each other, and not the
    signer. -/
lemma wd_accounts_new (hCompl : Groth16CompleteBytes) (π : Groth16.ProofBytes) :
    nullifierAccountsCreatable (W1 hCompl).state (wdInputs π)
    ∧ signerNotPoolNotNullifiers (wdInputs π) (W1 hCompl).state := by
  have hfresh := fun i => wd_fresh hCompl π i
  simp only [nullifierAccountsCreatable, signerNotPoolNotNullifiers, State.newNullifierAccount, wd_acct]
  simp only [State.spent, wd_acct, not_or] at hfresh
  have hz : (0 : Pubkey) ∉ (W1 hCompl).state.nullifierAccounts := by
    rw [W1_accounts]; simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨(toyAddr_ne_small _ _ 0 (by norm_num)).symm, (toyAddr_ne_small _ _ 0 (by norm_num)).symm⟩
  refine ⟨⟨toyAddr_ne (Or.inl (by decide)),
    toyAddr_notProgram _ (W1_pool hCompl) rfl rfl _ _ (hfresh 0).1,
    toyAddr_notProgram _ (W1_pool hCompl) rfl rfl _ _ (hfresh 1).2⟩,
    zero_notProgram _ (W1_pool hCompl) rfl rfl hz,
    (toyAddr_ne_small _ _ 0 (by norm_num)).symm, (toyAddr_ne_small _ _ 0 (by norm_num)).symm⟩

lemma wd_relation (π : Groth16.ProofBytes) : RelationS (wdInputs π).pubInputs wdWitness where
  outputCommitmentIntegrity := by
    intro j; fin_cases j <;> simp [wdInputs, TxInputs.pubInputs, wdWitness, commit, toy_H4]
  nullifierCorrectness := wd_nullifiers π
  noDuplicateNullifiers := by
    simp only [wdInputs, TxInputs.pubInputs, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ne_14_21
  correctOpenings := fun i _ => toy_valid _ _
  amountConservation := by simp [wdInputs, TxInputs.pubInputs, wdWitness]
  outputRangeChecks := by intro j; simp [wdWitness]

noncomputable def wdProof (hCompl : Groth16CompleteBytes) : Groth16.ProofBytes :=
  Classical.choose (hCompl (wdInputs ⟨[], [], []⟩).pubInputs wdWitness (wd_relation _))

noncomputable abbrev toyWithdrawal (hCompl : Groth16CompleteBytes) : TxInputs := wdInputs (wdProof hCompl)

/-- The toy withdrawal is an honest spend of the deposit's note, against the current root. -/
lemma toy_withdrawal_honest (hCompl : Groth16CompleteBytes) :
    HonestSpend (toyRun1 hCompl) (fun _ => toyWitness) (toyWithdrawal hCompl) wdWitness 2 := by
  have hcap2 : ((leaves (toyRun1 hCompl).txs).take 2).length < 2^26 := by
    rw [List.length_take, leaves_length]; simp [toyRun1]
  have hfin := toyRun1_final hCompl
  refine { genuine := ?_, notDoubleSpend := ?_, inputNotUsedBefore := ?_,
           root := { isPrefix := by simp [toyRun1]
                     isPrefixRoot := by rw [Run.firstLeaves, toy_root _ hcap2]; rfl },
           circuit := wd_relation _,
           wellFormed := { validProof := ?_, externalData := rfl, publicAmount := ?_,
                           amountRange := ?_, encOutLength := ?_, encodings := wd_encoded _,
                           poolNotRecipient := ?_, signed := by simp [signerSigned, wdInputs], solMint := rfl },
           signerCanPay := ?_, signerNotPoolNotNullifiers := by rw [hfin]; exact (wd_accounts_new hCompl _).2 }
  · intro i hne; fin_cases i
    · refine { inTree := ?_, ownsNote := ?_, knowsNote := ?_ }
      · simp [Witness.openedPos, wdWitness]
      · simp [leafNote, Witness.outNote, Witness.openedPos, wdWitness, toyWitness, toy_H1]
      · simp [leafNote, Witness.outNote, Witness.openedPos, wdWitness, toyWitness]
    · simp [wdWitness] at hne
  · -- input 1 has zero amount
    rintro ⟨-, h1, -⟩; simp [wdWitness] at h1
  · -- the run's inputs have commitment `0`, the withdrawal's have commitments `2` and `1`
    rintro i ⟨j, hj, i', hc, -⟩
    have h0 : toyWitness.inC i' = 0 := by
      simp [Witness.inC, commit, toyWitness, Witness.inPk, toy_H1, toy_H4]
    have h1 : wdWitness.inC i ≠ 0 := by
      have h20 : (2 : F) ≠ 0 := by
        have := natCast_ne_zero 2 (by norm_num) (by norm_num [p]); exact_mod_cast this
      fin_cases i <;> simp [Witness.inC, commit, wdWitness, Witness.inPk, toy_H1, toy_H4, h20, one_ne_zero_F]
    have hc' : toyWitness.inC i' = wdWitness.inC i := hc
    rw [h0] at hc'
    exact h1 hc'.symm
  · -- the proof Groth16 completeness gives for the withdrawal
    obtain ⟨π, hdec, hver⟩ := Classical.choose_spec
        (hCompl (wdInputs ⟨[], [], []⟩).pubInputs wdWitness (wd_relation _))
    exact ⟨π, hdec, hver⟩
  · simp [pubAmtConsistent, wdInputs]; norm_num
  · simp [amountsInRange, wdInputs]
  · simp [encOutsFit, wdInputs]
  · rw [hfin, W1_pool]; exact ⟨fun _ => toyPool_ne, fun _ => toyPool_ne⟩
  · rw [hfin]; unfold signerSolvent
    simp [topUp_zero (W1 hCompl) (W1_rent hCompl).1, wdInputs]

lemma wdWitness_real : wdWitness.inAmt 0 ≠ 0 := by
  simp only [wdWitness, Matrix.cons_val_zero]
  have := natCast_ne_zero 2 (by norm_num) (by norm_num [p]); exact_mod_cast this

/-! ### The run of both transactions -/

lemma toy_withdrawal_step (hCompl : Groth16CompleteBytes) :
    transact (toyWithdrawal hCompl) (W1 hCompl) (transactEffects (toyWithdrawal hCompl) (W1 hCompl)) := by
  refine ⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
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
    pubAmtConsistency := by simp [pubAmtConsistent, wdInputs]; norm_num
    validZKP := ⟨π, hdec, hver⟩
    newNullifiers := ⟨wd_fresh hCompl (wdProof hCompl) 0, wd_fresh hCompl (wdProof hCompl) 1⟩
    distinctNullifiers := ne_14_21
    nullifierAccountsNew := (wd_accounts_new hCompl _).1
    depositLimit := by simp [depositWithinLimit, wdInputs]
    poolSolvency := by
      refine ⟨fun _ => ?_, fun h => by simp [wdInputs] at h⟩
      rw [W1_poolBalance, hrent]; simp [wdInputs]
    signerSolvency := by
      unfold signerSolvent; simp [topUp_zero (W1 hCompl) (W1_rent hCompl).1, wdInputs]
    treeNotFull := by unfold treeHasRoom; rw [W1_nextIndex]; norm_num
    amountRange := by simp [amountsInRange, wdInputs]
    encOutLength := by simp [encOutsFit, wdInputs]
    poolNotRecipient := by rw [W1_pool]; exact ⟨fun _ => toyPool_ne, fun _ => toyPool_ne⟩
    signerSignature := by simp [signerSigned, wdInputs]
    solMint := rfl
    signerNotPoolNotNullifiers := (wd_accounts_new hCompl _).2
  }

/-- The run of the deposit followed by the withdrawal. -/
noncomputable def toyRun2 (hCompl : Groth16CompleteBytes) : Run toyInit where
  txs := [toyDeposit hCompl, toyWithdrawal hCompl]
  ws := fun j => if j = 0 then toyInit else if j = 1 then W1 hCompl
    else transactEffects (toyWithdrawal hCompl) (W1 hCompl)
  updatedValues := fun j =>
    UpdatedValuesBetweenTransacts.unchanged (if j = 0 then toyInit else if j = 1 then W1 hCompl
    else transactEffects (toyWithdrawal hCompl) (W1 hCompl))
  start := rfl
  allowed := fun j hj => by
    rcases (show j = 0 ∨ j = 1 by simp at hj; omega) with rfl | rfl
    · exact UpdatedValuesBetweenTransacts.Allowed.self _ toyInit_fit
    · exact UpdatedValuesBetweenTransacts.Allowed.self _
        (fun x => show (W1 hCompl).balances x < 2 ^ 64 by have := W1_bal hCompl x; omega)
  step := by
    intro j hj
    simp only [List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · simpa [World.withUpdatedValues_self] using toy_deposit_step hCompl
    · simpa [World.withUpdatedValues_self] using toy_withdrawal_step hCompl

theorem run_with_spend_exists (hCompl : Groth16CompleteBytes) :
    ∃ (params : InitParams) (r : Run (initWorld params)) (wit : ℕ → Witness),
      r.txs.length = 2 ∧ r.WitnessesFor wit ∧ (wit 1).inAmt 0 ≠ 0 ∧ openedPos wit 1 0 = 0
      ∧ (wit 1).inNote 0 = leafNote wit 0 := by
  refine ⟨toyParams, toyRun2 hCompl, fun j => if j = 0 then toyWitness else wdWitness, rfl, ?_, ?_,
    rfl, ?_⟩
  · intro j hj
    simp only [toyRun2, List.length_cons, List.length_nil] at hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact fun _ => toy_relation _
    · exact fun _ => wd_relation _
  · exact wdWitness_real
  · simp [Witness.inNote, leafNote, Witness.outNote, Witness.inPk, wdWitness, toyWitness, toy_H1]


/-- **The toy withdrawal is accepted.** After `toyRun1`, the program accepts the withdrawal of
    the deposit's note. -/
theorem toy_withdrawal_accepted (hCompl : Groth16CompleteBytes) :
    CanBeAccepted (toyWithdrawal hCompl) (toyRun1 hCompl).final := by
  rw [toyRun1_final]
  exact toy_withdrawal_step hCompl

/-- **The hypotheses of G3a can all hold, on a real spend, and the program accepts it.** After
    `toyRun1`, withdrawing the deposit's note against the current root (`k = 2`). -/
theorem toy_G3_hypotheses (hCompl : Groth16CompleteBytes) :
    ∃ (params : InitParams) (r : Run (initWorld params)) (wit : ℕ → Witness) (inputs : TxInputs)
      (witness : Witness) (k : ℕ),
      r.WitnessesFor wit ∧ HonestSpend r wit inputs witness k ∧ LimitsNotHit r.final inputs
      ∧ witness.inAmt 0 ≠ 0 ∧ CanBeAccepted inputs r.final := by
  have hfin := toyRun1_final hCompl
  refine ⟨toyParams, toyRun1 hCompl, fun _ => toyWitness, toyWithdrawal hCompl, wdWitness, 2,
    toyRun1_wit hCompl, toy_withdrawal_honest hCompl, ?_, wdWitness_real, toy_withdrawal_accepted hCompl⟩
  refine { inWindow := by rw [hfin]; exact W1_root_mem hCompl, treeRoom := ?_,
           balancesFit := by rw [hfin]; exact wd_fit hCompl _, fee := ?_, depositLimit := ?_ }
  · rw [hfin]; unfold treeHasRoom; rw [W1_nextIndex]; norm_num
  · rw [hfin]; simp [feeSufficient, W1, transactEffects, transferEffects_state, initWorld, toyCfg, wdInputs]
  · simp [depositWithinLimit, wdInputs]

/-! ### Every split of that note between recipient and fee -/

/-- The toy withdrawal, paying `payout` to the recipient and `fee` as the fee. -/
def wdSplit (payout fee : ℕ) (π : Groth16.ProofBytes) : TxInputs :=
  { wdInputs π with extAmt := -(payout : ℤ), f := fee }

lemma split_cases {payout fee : ℕ} (h : payout + fee = 2) :
    (payout = 0 ∧ fee = 2) ∨ (payout = 1 ∧ fee = 1) ∨ (payout = 2 ∧ fee = 0) := by omega

lemma wdSplit_fit (hCompl : Groth16CompleteBytes) (π : Groth16.ProofBytes) {payout fee : ℕ}
    (h : payout + fee = 2) : balancesFit (wdSplit payout fee π) (W1 hCompl) := by
  refine ⟨fun k _ => ?_, fun h' => by simp [wdSplit] at h'; omega⟩
  have h1 := W1_bal hCompl k
  have h2 : balanceDelta (wdSplit payout fee π) (W1 hCompl) k ≤ 2 := by
    unfold balanceDelta
    simp only [topUp_zero (W1 hCompl) (W1_rent hCompl).1, Nat.cast_zero, add_zero, ite_self,
      sub_zero]
    rcases split_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      (split_ifs <;> simp_all [wdSplit, wdInputs])
  linarith

/-- With any split, the toy withdrawal is an honest spend of the deposit's note: only the amounts
    differ from `toy_withdrawal_honest`. -/
lemma toy_split_honest (hCompl : Groth16CompleteBytes) {payout fee : ℕ} (h : payout + fee = 2) :
    HonestSpend (toyRun1 hCompl) (fun _ => toyWitness) (wdSplit payout fee (wdProof hCompl))
      wdWitness 2 := by
  have hw := toy_withdrawal_honest hCompl
  have hfin := toyRun1_final hCompl
  refine { genuine := hw.genuine, notDoubleSpend := hw.notDoubleSpend,
           inputNotUsedBefore := hw.inputNotUsedBefore, root := ?_, circuit := hw.circuit,
           wellFormed := { validProof := hw.wellFormed.validProof, externalData := rfl,
                           publicAmount := ?_, amountRange := ?_,
                           encOutLength := hw.wellFormed.encOutLength,
                           encodings := hw.wellFormed.encodings,
                           poolNotRecipient := ?_, signed := hw.wellFormed.signed, solMint := rfl },
           signerCanPay := ?_, signerNotPoolNotNullifiers := by rw [hfin]; exact (wd_accounts_new hCompl (wdProof hCompl)).2 }
  · have hcap2 : ((leaves (toyRun1 hCompl).txs).take 2).length < 2^26 := by
      rw [List.length_take, leaves_length]; simp [toyRun1]
    exact { isPrefix := by simp [toyRun1]
            isPrefixRoot := by rw [Run.firstLeaves, toy_root _ hcap2]; rfl }
  · rcases split_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [pubAmtConsistent, wdSplit, wdInputs]; norm_num
  · rcases split_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [amountsInRange, wdSplit, wdInputs]
  · rw [hfin, W1_pool]; exact ⟨fun _ => toyPool_ne, fun _ => toyPool_ne⟩
  · rw [hfin]; unfold signerSolvent
    simp only [topUp_zero (W1 hCompl) (W1_rent hCompl).1]
    rcases split_cases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [wdSplit, wdInputs]

/-- **The hypotheses of G3b's `WayIsAccepted` can all hold, on a real spend, for every split.**
    After the deposit, withdrawing its 2-lamport note with any payout and fee that add up to 2. -/
theorem toy_G3b_hypotheses (hCompl : Groth16CompleteBytes) :
    ∃ (params : InitParams) (r : Run (initWorld params)) (wit : ℕ → Witness),
      r.WitnessesFor wit
      ∧ ∀ payout fee : ℕ, payout + fee = 2 →
        ∃ (inputs : TxInputs) (witness : Witness) (k : ℕ),
          HonestSpend r wit inputs witness k
          ∧ witness.inAmt 0 ≠ 0
          ∧ witness.inAmt 0 + witness.inAmt 1 = ((2 : ℕ) : F)
          ∧ inputs.extAmt = -(payout : ℤ) ∧ inputs.f = fee
          ∧ inputs.R ∈ Set.range r.final.state.tree.history
          ∧ treeHasRoom r.final.state.tree
          ∧ balancesFit inputs r.final := by
  have hfin := toyRun1_final hCompl
  refine ⟨toyParams, toyRun1 hCompl, fun _ => toyWitness, toyRun1_wit hCompl, fun payout fee h =>
    ⟨wdSplit payout fee (wdProof hCompl), wdWitness, 2, toy_split_honest hCompl h, wdWitness_real,
      by simp [wdWitness], rfl, rfl, ?_, ?_, ?_⟩⟩
  · rw [hfin]; exact W1_root_mem hCompl
  · rw [hfin]; unfold treeHasRoom; rw [W1_nextIndex]; norm_num
  · rw [hfin]; exact wdSplit_fit hCompl _ h

/-- **The hypotheses of G4a and G4b can hold.** The toy withdrawal is accepted. -/
theorem toy_G4_hypotheses (hCompl : Groth16CompleteBytes) :
    ∃ (inputs : TxInputs) (oldWorld newWorld : World), transact inputs oldWorld newWorld :=
  ⟨_, _, _, toy_withdrawal_accepted hCompl⟩

/-- **The hypotheses of G2a can hold together.** The toy withdrawal, as both the honest and the
    attacker's transaction: it is well formed (its external data hashes to what its proof
    commits to, and its amounts and encrypted outputs are in range), and it is accepted. -/
theorem toy_G2a_hypotheses (hCompl : Groth16CompleteBytes) :
    ∃ (T T' : TxInputs) (oldWorld' newWorld' : World),
      (externalDataBound T ∧ amountsInRange T.extAmt T.f ∧ encOutsFit T)
      ∧ T.pubInputs = T'.pubInputs ∧ transact T' oldWorld' newWorld' := by
  have h := toy_withdrawal_accepted hCompl
  exact ⟨_, _, _, _, ⟨h.1.externalDataBinding, h.1.amountRange, h.1.encOutLength⟩, rfl, h⟩

/-- **The hypotheses of G2b can hold together.** The toy withdrawal's witness, as both
    witnesses: it satisfies the circuit for its public inputs, so the two share a nullifier. -/
theorem toy_G2b_hypotheses (hCompl : Groth16CompleteBytes) :
    ∃ (x : PubInputs) (w : Witness) (x' : PubInputs) (w' : Witness) (i i' : Fin 2),
      RelationS x w ∧ RelationS x' w' ∧ x.nullifiers i = x'.nullifiers i' :=
  have h := (toy_withdrawal_honest hCompl).circuit
  ⟨_, _, _, _, 0, 0, h, h, rfl⟩

end LeanSpec.NonVacuity

namespace LeanSpec.NonVacuity
open LeanSpec

attribute [local instance] toyGroups toyG1Group toyG2Group toyG1Module toyG2Module toyGTGroup
  toyPairing toyDeployment


/-- Toy completeness on the wire: in the toy groups every proof verifies, and the empty bytes
    decode to the point `0`. -/
theorem toyCompleteBytes [PoseidonHashes] [Sha] : Groth16CompleteBytes :=
  have h1 : Groups.decodeG1 [] = some (0 : G1) := congrArg some Nat.cast_zero
  have h2 : Groups.decodeG2 [] = some (0 : G2) := congrArg some Nat.cast_zero
  fun _ _ _ => ⟨⟨[], [], []⟩, ⟨0, 0, 0⟩, by simp [Groth16.ProofBytes.decode, h1, h2], rfl⟩

end LeanSpec.NonVacuity
