import Connection.Proofs.ToyRun
import Connection.Proofs.Execution
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # A toy execution with a real spend (not for review)

The toy execution of `Connection/Proofs/ToyRun.lean` (genesis, `initialize`, a deposit of 2
lamports), followed by a withdrawal that spends the note the deposit created: 1 lamport with a fee
of 1, or 2 lamports with no fee (`ToySplit`).
Every hypothesis of `run_connection` holds for the three-step execution, and every spec run of
it has circuit witnesses in which the withdrawal's first input is the deposit's note, with a
non-zero amount (`toy_spend_nonvacuous`). The deposit and the withdrawal each satisfy every
hypothesis of `transact_connection` (`toy_transact_nonvacuous`).

The code never computes `H1`, `H3`, `H4` (only the circuit does), so the toy chooses them
(`toyPoseidon`: `H1` the identity, `H3`, `H4` sums) such that witnesses exist for the
nullifiers and commitments the toy transactions send. -/

namespace Connection.Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha

/-! ## The withdrawal's bytes and accounts -/

def three32 : Std.Array U8 32#usize := Std.Array.make 32#usize (List.replicate 31 0#u8 ++ [3#u8]) (by simp)

/-- `p - 2`, the field's `-2`, as 32 bytes big-endian: the public amount of a withdrawal of 1
    lamport with a fee of 1. -/
def minusTwo32 : Std.Array U8 32#usize := Std.Array.make 32#usize
  [0x30#u8, 0x64#u8, 0x4e#u8, 0x72#u8, 0xe1#u8, 0x31#u8, 0xa0#u8, 0x29#u8, 0xb8#u8, 0x50#u8,
   0x45#u8, 0xb6#u8, 0x81#u8, 0x81#u8, 0x58#u8, 0x5d#u8, 0x28#u8, 0x33#u8, 0xe8#u8, 0x48#u8,
   0x79#u8, 0xb9#u8, 0x70#u8, 0x91#u8, 0x43#u8, 0xe1#u8, 0xf5#u8, 0x93#u8, 0xef#u8, 0xff#u8,
   0xff#u8, 0xff#u8] (by simp)

theorem beNat_three32 : beNat three32 = 3 := by rfl
theorem beNat_minusTwo32 : beNat minusTwo32 = bn254ScalarModulus - 2 := by rfl
theorem toF_three32 : toF three32 = 3 := by simp only [toF, beNat_three32]; rfl
theorem toF_minusTwo32 : toF minusTwo32 = -2 := by
  rw [toF, beNat_minusTwo32, ← p_eq, Nat.cast_sub (by decide), ZMod.natCast_self, zero_sub]; rfl
theorem canonical_three32 : Canonical three32 := by simp only [Canonical, beNat_three32]; decide
theorem canonical_minusTwo32 : Canonical minusTwo32 := by
  simp only [Canonical, beNat_minusTwo32]; decide

/-- The withdrawal's proof bytes: root `1`, public amount `-2`, nullifiers `2` and `3`, two
    zero output commitments. The proof points are those of the toy deposit. -/
def spendProof : transact.Proof :=
  { proof_a := verifying_key.VERIFYING_KEY.vk_alpha_g1, proof_b := Std.Array.repeat 128#usize 0#u8,
    proof_c := zeros64, root := one32, public_amount := minusTwo32, ext_data_hash := zeros32,
    input_nullifiers := Std.Array.make 2#usize [two32, three32] (by simp),
    output_commitments := Std.Array.make 2#usize [zeros32, zeros32] (by simp) }

def wdExt : I64 := (-1)#i64

def nf0W : Pubkey := toyD.pda (nullifier0Seeds two32)
def nf1W : Pubkey := toyD.pda (nullifier1Seeds three32)
def nf2W : Pubkey := toyD.pda (nullifier0Seeds three32)
def nf3W : Pubkey := toyD.pda (nullifier1Seeds two32)

/-- The withdrawal's accounts: as the deposit's, with the new nullifiers' addresses. -/
def spendA : TransactAccounts :=
  { treeAccount := treeA, nullifier0 := nf0W, nullifier1 := nf1W, nullifier2 := nf2W,
    nullifier3 := nf3W, treeTokenAccount := tokenA, globalConfig := configA,
    recipient := pk 3#u8, feeRecipientAccount := pk 4#u8, signer := pk 1#u8,
    systemProgram := systemProgram }

/-- The addresses the withdrawal uses are distinct where it matters. -/
theorem spend_addr : nf0W ≠ treeA ∧ nf0W ≠ tokenA ∧ nf0W ≠ configA ∧ nf0W ≠ pk 1#u8 ∧
    nf0W ≠ nf0A ∧ nf0W ≠ nf1A ∧
    nf1W ≠ treeA ∧ nf1W ≠ tokenA ∧ nf1W ≠ configA ∧ nf1W ≠ pk 1#u8 ∧ nf1W ≠ nf0A ∧ nf1W ≠ nf1A ∧
    nf0W ≠ nf1W ∧
    nf2W ≠ treeA ∧ nf2W ≠ tokenA ∧ nf2W ≠ configA ∧ nf2W ≠ pk 1#u8 ∧ nf2W ≠ nf0A ∧ nf2W ≠ nf1A ∧
    nf3W ≠ treeA ∧ nf3W ≠ tokenA ∧ nf3W ≠ configA ∧ nf3W ≠ pk 1#u8 ∧ nf3W ≠ nf0A ∧ nf3W ≠ nf1A ∧
    pk 3#u8 ≠ nf0W ∧ pk 3#u8 ≠ nf1W ∧ pk 4#u8 ≠ nf0W ∧ pk 4#u8 ≠ nf1W ∧
    pk 3#u8 ≠ nf0A ∧ pk 3#u8 ≠ nf1A := by
  unfold nf0W nf1W nf2W nf3W nf0A nf1A treeA tokenA configA
  decide +kernel

theorem wdExt_val : wdExt.val = -1 := by simp [wdExt]

/-- The two ways the withdrawal can split the note's 2 lamports: 1 to the recipient and a fee of
    1, or 2 to the recipient and no fee. -/
def ToySplit (ext : I64) (fee : U64) : Prop :=
  (ext.val = -1 ∧ fee.val = 1) ∨ (ext.val = -2 ∧ fee.val = 0)

theorem toySplit_one : ToySplit wdExt 1#u64 := Or.inl ⟨wdExt_val, by simp⟩
theorem toySplit_two : ToySplit (-2)#i64 0#u64 := Or.inr ⟨by simp, by simp⟩

/-! ## The circuit witnesses (spec side)

With `H3`, `H4` sums and `H1` the identity, a note's commitment is `amt + sk + r + mint`, and
the nullifier of an input at leaf `idx` is `sk + 2·c + 2·idx`. -/

/-- The deposit: two zero-amount inputs at leaf 0 (keys `0` and `1`, nullifiers `0` and `1`);
    output 0 is a note of 2 lamports owned by the key `2` (commitment `2 + 2 - 4 = 0`). -/
def depWit : LeanSpec.Witness where
  mint := 0
  inAmt := 0
  inSk := ![0, 1]
  inR := ![0, -1]
  openings := fun _ => ⟨0, 0⟩
  outAmt := ![2, 0]
  outPk := ![2, 0]
  outR := ![-4, 0]

/-- The withdrawal: input 0 spends the deposit's note (leaf 0, key `2`, nullifier `2`); input 1
    is a zero-amount input with key `3` (nullifier `3`). Both outputs are empty. -/
def spendWit : LeanSpec.Witness where
  mint := 0
  inAmt := ![2, 0]
  inSk := ![2, 3]
  inR := ![-4, -3]
  openings := fun _ => ⟨0, 0⟩
  outAmt := 0
  outPk := 0
  outR := 0

theorem toy_H1 (a : LeanSpec.F) : LeanSpec.PoseidonHashes.H1 a = a := rfl
theorem toy_H3 (a b c : LeanSpec.F) : LeanSpec.PoseidonHashes.H3 a b c = a + b + c := rfl
theorem toy_H4 (a b c d : LeanSpec.F) : LeanSpec.PoseidonHashes.H4 a b c d = a + b + c + d := rfl

/-- In the toy every Merkle path reaches the root `1`. -/
theorem toy_calcRoot (O : LeanSpec.Opening) (c : LeanSpec.F) : O.calcRoot c = 1 := by
  unfold LeanSpec.Opening.calcRoot
  rw [Fin.foldl_succ_last]
  split_ifs <;> rfl

/-- In the toy every root an append stores is `1`. -/
theorem toy_append_history (c : LeanSpec.F) (T : LeanSpec.Tree) :
    (LeanSpec.appendEffects c T).history (T.rootIndex + 1) = 1 := by
  unfold LeanSpec.appendEffects
  simp only [Function.update_self]
  rw [Fin.foldl_succ_last]
  split_ifs <;> rfl

theorem dep_relation :
    LeanSpec.RelationS (toInputs toyTx.signers depA depProof 2#i64 0#u64 emptySlice emptySlice).pubInputs depWit where
  outputCommitmentIntegrity := by
    intro j
    fin_cases j <;>
      simp [toInputs, LeanSpec.TxInputs.pubInputs, depProof, toyProof, toF_zeros32, depWit,
        LeanSpec.commit, toy_H4]
    all_goals norm_num
  nullifierCorrectness := by
    intro i
    fin_cases i <;>
      simp [toInputs, LeanSpec.TxInputs.pubInputs, depProof, toyProof, toF_zeros32, toF_one32, depWit,
        LeanSpec.nullifier, LeanSpec.Witness.sign, LeanSpec.signature, LeanSpec.Witness.inC,
        LeanSpec.commit, LeanSpec.Witness.inPk, toy_H1, toy_H3, toy_H4]
  noDuplicateNullifiers := by
    simp only [toInputs, LeanSpec.TxInputs.pubInputs, Matrix.cons_val_zero, Matrix.cons_val_one]
    show toF zeros32 ≠ toF one32
    rw [toF_zeros32, toF_one32]; decide
  correctOpenings := by intro i hi; simp [depWit] at hi
  amountConservation := by
    simp [toInputs, LeanSpec.TxInputs.pubInputs, depProof, toyProof, toF_two32, depWit]
  outputRangeChecks := by
    haveI : Fact (1 < LeanSpec.p) := ⟨by norm_num [LeanSpec.p]⟩
    have hval : ZMod.val (2 : LeanSpec.F) = 2 := by
      have := ZMod.val_natCast_of_lt (n := LeanSpec.p) (a := 2) (by norm_num [LeanSpec.p]); exact_mod_cast this
    intro j; fin_cases j <;> simp [depWit, hval]

theorem spend_relation {ext : I64} {fee : U64} :
    LeanSpec.RelationS (toInputs toyTx.signers spendA spendProof ext fee emptySlice emptySlice).pubInputs spendWit where
  outputCommitmentIntegrity := by
    intro j
    fin_cases j <;>
      simp [toInputs, LeanSpec.TxInputs.pubInputs, spendProof, toF_zeros32, spendWit, LeanSpec.commit, toy_H4]
  nullifierCorrectness := by
    intro i
    fin_cases i <;>
      simp [toInputs, LeanSpec.TxInputs.pubInputs, spendProof, toF_two32, toF_three32, spendWit,
        LeanSpec.nullifier, LeanSpec.Witness.sign, LeanSpec.signature, LeanSpec.Witness.inC,
        LeanSpec.commit, LeanSpec.Witness.inPk, toy_H1, toy_H3, toy_H4]
    all_goals norm_num
  noDuplicateNullifiers := by
    simp only [toInputs, LeanSpec.TxInputs.pubInputs, Matrix.cons_val_zero, Matrix.cons_val_one]
    show toF two32 ≠ toF three32
    rw [toF_two32, toF_three32]; decide
  correctOpenings := by
    intro i _
    show LeanSpec.Opening.calcRoot _ _ = toF one32
    rw [toF_one32]; exact toy_calcRoot _ _
  amountConservation := by
    simp [toInputs, LeanSpec.TxInputs.pubInputs, spendProof, toF_minusTwo32, spendWit]
  outputRangeChecks := by intro j; simp [spendWit]

/-! ## The withdrawal is accepted -/

/-- The withdrawal's spec preconditions, from the handler's view after the two nullifier
    `init`s: the tree is the deposit's tree (two appends after `initialize`), the pool holds 3
    lamports, the recipient and the fee recipient none. -/
theorem spend_pre (sB : State) (tree₂ t1 : merkle_tree.MerkleTreeAccount) (config : admin.GlobalConfig)
    (c : LeanSpec.F) (htree : toTree tree₂ = LeanSpec.appendEffects c (toTree t1))
    (hTn : tree₂.next_index.val = 2) (hwr : config.withdrawal_fee_rate.val = 25)
    (hpoolB : (sB tokenA).lamports.val = 3) (hrecB : (sB (pk 3#u8)).lamports.val = 0)
    (hfeeB : (sB (pk 4#u8)).lamports.val = 0) {ext : I64} {fee : U64} (hsplit : ToySplit ext fee) :
    HandlerPre Unit Unit Unit toyTx.signers toyCrypto toyC spendA sB 1#u64 tree₂ config ∅ spendProof ext fee
      emptySlice emptySlice := by
  unfold HandlerPre
  have hsp := hsplit; unfold ToySplit at hsp
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hTP, -⟩ := dep_addr
  have hdec := decode_toInputs (signers := toyTx.signers) toyC spendProof spendA ext 0#u64 emptySlice emptySlice
    toy_alpha_decodes rfl toy_zeros_decodes
  have he : (toInputs toyTx.signers spendA spendProof ext fee emptySlice emptySlice).extAmt = ext.val := rfl
  have hf : (toInputs toyTx.signers spendA spendProof ext fee emptySlice emptySlice).f = fee.val := rfl
  have h3P : pk 3#u8 ≠ tokenA := by unfold tokenA; decide +kernel
  have h4P : pk 4#u8 ≠ tokenA := by unfold tokenA; decide +kernel
  have hpool : (handlerWorld spendA sB 1#u64 tree₂ config ∅).state.pool = toPubkey tokenA := rfl
  have hnr : (handlerWorld spendA sB 1#u64 tree₂ config ∅).nullifierRent = 0 := rfl
  have hA : (toInputs toyTx.signers spendA spendProof ext fee emptySlice emptySlice).A = toPubkey (pk 3#u8) := rfl
  have hs : (toInputs toyTx.signers spendA spendProof ext fee emptySlice emptySlice).s = toPubkey (pk 1#u8) := rfl
  have ht : (toInputs toyTx.signers spendA spendProof ext fee emptySlice emptySlice).t = toPubkey (pk 4#u8) := rfl
  have hpb : (handlerWorld spendA sB 1#u64 tree₂ config ∅).balances (toPubkey tokenA) = 3 := by
    show (sB (fromPubkey (toPubkey tokenA))).lamports.val = 3
    rw [fromPubkey_toPubkey, hpoolB]
  refine @LeanSpec.transactPreconditions.mk _ (syscallGroups toyC) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit))
    (inferInstanceAs (CommGroup Unit))
    (syscallPairing toyC) (@LeanSpec.Deployment.mk (syscallGroups toyC) (programKey toyC)) _ _
    ?_ ?_ ?_ ?_ ⟨_, hdec, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the root: the deposit's last append stored the root `1`
    show LeanSpec.rootBytesKnown (toTree tree₂) (toBytes one32.val)
    rw [rootBytesKnown_iff]
    refine ⟨canonical_one32, ⟨⟨(toTree t1).rootIndex + 1, ?_⟩, by rw [toF_one32]; decide⟩⟩
    rw [htree, toy_append_history, toF_one32]
  · show (LeanSpec.natOfLE (List.replicate 32 0) : LeanSpec.F) = toF zeros32
    rw [toF_zeros32]; rfl
  · unfold LeanSpec.feeSufficient; rw [he, hf]; simp [handlerWorld, toConfig, hwr]
    rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · unfold LeanSpec.pubAmtConsistent; rw [he, hf]
    refine ⟨fun h => by omega, ?_⟩
    show toF minusTwo32 = _; rw [toF_minusTwo32]
    rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2] <;> norm_num
  · simp [LeanSpec.nullifiersFresh, handlerWorld]
  · show toF two32 ≠ toF three32
    rw [toF_two32, toF_three32]; decide
  · intro h; rw [he] at h; omega
  · unfold LeanSpec.poolSolvent; rw [he, hf]
    refine ⟨fun _ => ?_, fun h => by omega⟩
    have hpb' : (handlerWorld spendA sB 1#u64 tree₂ config ∅).poolBalance = 3 := hpb
    rw [hpb']; simp [handlerWorld]
    rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp [h1, h2]
  · unfold LeanSpec.signerSolvent; rw [he]; simp [handlerWorld]
    rcases hsp with ⟨h1, -⟩ | ⟨h1, -⟩ <;> simp [h1]
  · exact List.mem_map_of_mem (f := toPubkey) (List.mem_singleton.mpr rfl)
  · show (toTree tree₂).nextIndex ≤ 2 ^ 26 - 2; simp [toTree, hTn]
  · unfold LeanSpec.amountsInRange; rw [he, hf]; omega
  · simp [LeanSpec.encOutsFit, toInputs, emptySlice, toBytes]
  · exact ⟨fun e => (Ne.symm hTP) (toPubkey_inj e), fun _ e => h3P (toPubkey_inj e),
      fun _ e => h4P (toPubkey_inj e)⟩
  · intro i
    show LeanSpec.canonicalEncoding (toBytes ((publicInputs _)[i.val]!).val) _
    rw [canonicalEncoding_iff]
    fin_cases i
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_minusTwo32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_two32, rfl⟩
    · exact ⟨canonical_three32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
  · refine ⟨fun k hk => ?_, fun h => by rw [he] at h; omega⟩
    -- only the recipient and the fee recipient are credited, and they hold nothing
    unfold LeanSpec.balanceDelta at hk ⊢
    rw [he, hf, hpool, hnr, hA, hs, ht] at hk ⊢
    by_cases hk3 : k = toPubkey (pk 3#u8)
    · subst hk3
      have hb : (handlerWorld spendA sB 1#u64 tree₂ config ∅).balances (toPubkey (pk 3#u8)) = 0 := by
        show (sB (fromPubkey (toPubkey (pk 3#u8)))).lamports.val = 0
        rw [fromPubkey_toPubkey, hrecB]
      rw [hb]
      have h3p : toPubkey (pk 3#u8) ≠ toPubkey tokenA := fun e => h3P (toPubkey_inj e)
      simp only [h3p, if_false]
      split_ifs <;> omega
    by_cases hk4 : k = toPubkey (pk 4#u8)
    · subst hk4
      have hb : (handlerWorld spendA sB 1#u64 tree₂ config ∅).balances (toPubkey (pk 4#u8)) = 0 := by
        show (sB (fromPubkey (toPubkey (pk 4#u8)))).lamports.val = 0
        rw [fromPubkey_toPubkey, hfeeB]
      rw [hb]
      have h4p : toPubkey (pk 4#u8) ≠ toPubkey tokenA := fun e => h4P (toPubkey_inj e)
      simp only [h4p, if_false]
      split_ifs <;> omega
    · exfalso
      simp only [hk3, hk4, false_and, if_false] at hk
      split_ifs at hk <;> omega

/-- **The withdrawal is accepted by `step`**, from the state after the deposit. -/
theorem toy_spend_ok (s₂ : State) (tree₂ t1 : merkle_tree.MerkleTreeAccount) (token : admin.TreeTokenAccount)
    (config : admin.GlobalConfig) (c : LeanSpec.F)
    (hT : s₂ treeA = ⟨1#u64, toyD.programId, .treeAccount tree₂⟩)
    (hK : s₂ tokenA = ⟨3#u64, toyD.programId, .treeToken token⟩)
    (hC : s₂ configA = ⟨1#u64, toyD.programId, .globalConfig config⟩)
    (hP : s₂ (pk 1#u8) = ⟨993#u64, systemProgram, .empty⟩)
    (hO : ∀ k, k ≠ treeA → k ≠ tokenA → k ≠ configA → k ≠ pk 1#u8 → k ≠ nf0A → k ≠ nf1A → s₂ k = toyS0 k)
    (hshape : TreeShape tree₂) (hroots : ∀ j : Fin 100, Canonical tree₂.root_history.val[j.val]!)
    (hsubs : ∀ j : Fin 26, Canonical tree₂.subtrees.val[j.val]!)
    (htree : toTree tree₂ = LeanSpec.appendEffects c (toTree t1)) (hTn : tree₂.next_index.val = 2)
    (hTb : tree₂.bump = 255#u8) (hkb : token.bump = 255#u8) (hcb : config.bump = 255#u8)
    (hdr : config.deposit_fee_rate.val = 0) (hwr : config.withdrawal_fee_rate.val = 25)
    (hmr : config.fee_error_margin.val = 500) {ext : I64} {fee : U64} (hsplit : ToySplit ext fee) :
    ∃ s' events, step toyD s₂ toyTx (.transact spendA spendProof ext fee emptySlice emptySlice)
      = .ok (s', events) := by
  obtain ⟨w01, w02, w03, w04, w05, w06, w11, w12, w13, w14, w15, w16, w0n1, w21, w22, w23, w24, w25, w26,
    w31, w32, w33, w34, w35, w36, p30, p31, q40, q41, p3a, p3b⟩ := spend_addr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p3T, p3K, p3C, p4T, p4K, p4C,
    -, -, -, -, hTP, -⟩ := dep_addr
  have p31' : pk 3#u8 ≠ pk 1#u8 := pk_ne (by decide)
  have h3P : pk 3#u8 ≠ tokenA := p3K
  have h4P : pk 4#u8 ≠ tokenA := p4K
  have p41' : pk 4#u8 ≠ pk 1#u8 := pk_ne (by decide)
  have p4a : pk 4#u8 ≠ nf0A := by unfold nf0A; decide +kernel
  have p4b : pk 4#u8 ≠ nf1A := by unfold nf1A; decide +kernel
  have hPs : s₂ spendA.signer = ⟨993#u64, systemProgram, .empty⟩ := hP
  have hz : ∀ k, k ≠ treeA → k ≠ tokenA → k ≠ configA → k ≠ pk 1#u8 → k ≠ nf0A → k ≠ nf1A →
      (s₂ k).lamports.val = 0 ∧ (s₂ k).owner = systemProgram ∧ (s₂ k).data = .empty := by
    intro k e1 e2 e3 e4 e5 e6
    rw [hO k e1 e2 e3 e4 e5 e6]; unfold toyS0; rw [if_neg e4]; exact ⟨rfl, rfl, rfl⟩
  -- the two nullifier inits, paid by the signer
  obtain ⟨sA, hA, oA, dA, lA, -, -, -, kA, mA⟩ := init_step (pid := toyD.programId)
    (space := nullifierAccountSpace) (data := .nullifier 0#u8) (s := s₂) (payer := spendA.signer)
    (key := spendA.nullifier0) (hz nf0W w01 w02 w03 w04 w05 w06).1 (by rw [hPs]) (by rw [hPs]; rfl)
    (by rw [hPs]; decide) (Ne.symm w04)
  have z1 : (sA spendA.nullifier1).lamports.val = 0 := by
    rw [kA spendA.nullifier1 w14 (Ne.symm w0n1)]; exact (hz nf1W w11 w12 w13 w14 w15 w16).1
  have lA' : (sA spendA.signer).lamports.val = 992 := by rw [lA, hPs]; rfl
  obtain ⟨sB, hB, oB, dB, lB, -, -, -, kB, mB⟩ := init_step (pid := toyD.programId)
    (space := nullifierAccountSpace) (data := .nullifier 0#u8) (s := sA) (payer := spendA.signer)
    (key := spendA.nullifier1) z1 (by rw [oA, hPs]) (by rw [dA, hPs]; rfl) (by rw [lA']; omega) (Ne.symm w14)
  have hsB : ∀ k, k ≠ pk 1#u8 → k ≠ nf0W → k ≠ nf1W → sB k = s₂ k := fun k h1 h2 h3 =>
    (kB k h1 h3).trans (kA k h1 h2)
  have hpoolB : (sB tokenA).lamports.val = 3 := by
    rw [hsB tokenA hTP (Ne.symm w02) (Ne.symm w12), hK]; rfl
  have hrecB : (sB (pk 3#u8)).lamports.val = 0 := by
    rw [hsB _ p31' p30 p31]; exact (hz _ p3T p3K p3C p31' p3a p3b).1
  have hfeeB : (sB (pk 4#u8)).lamports.val = 0 := by
    rw [hsB _ p41' q40 q41]; exact (hz _ p4T p4K p4C p41' p4a p4b).1
  -- the handler
  obtain ⟨ap, env', tree', hh⟩ := handler_ok_exists toyCrypto toyC toyLaws toyHashesAgree toyHashesSucceed
    toySyscalls toyKey spendA sB 1#u64 tree₂ config ∅ spendProof ext fee emptySlice emptySlice hshape
    hroots hsubs (by omega) (by omega) (by omega)
    ⟨by rw [oB, oA, hPs], by rw [dB, dA, hPs]; rfl⟩ toyFit (by rcases hsplit with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide) alpha_ne_zeros
    (spend_pre sB tree₂ t1 config c htree hTn hwr hpoolB hrecB hfeeB hsplit)
  -- lamports are conserved
  have hok := handler_ok toyCrypto _ _ _ _ _ _ _ _ _ _ _ _ _ hh
  obtain ⟨v', -, -, hwd, -⟩ := hok.rent
  have hneg : ext.val < 0 := by rcases hsplit with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> decide
  have hsum : ext.val.natAbs + fee.val = 2 := by
    rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rfl
  have he : (fun k => (env'.balances k).val) = payN (payN (fun k => (sB k).lamports.val) spendA.treeTokenAccount
      spendA.recipient ext.val.natAbs) spendA.treeTokenAccount spendA.feeRecipientAccount fee.val :=
    (hwd hneg).2
  set K := [spendA.treeAccount, spendA.nullifier0, spendA.nullifier1, spendA.nullifier2, spendA.nullifier3,
    spendA.treeTokenAccount, spendA.globalConfig, spendA.recipient, spendA.feeRecipientAccount, spendA.signer,
    spendA.systemProgram] with hK'
  have hTL : TL K (fun k => (env'.balances k).val) = TL K (fun k => (s₂ k).lamports.val) := by
    have hafter : fee.val ≤ payN (fun k => (sB k).lamports.val) spendA.treeTokenAccount spendA.recipient
        ext.val.natAbs spendA.treeTokenAccount := by
      show fee.val ≤ payN (fun k => (sB k).lamports.val) tokenA (pk 3#u8) ext.val.natAbs tokenA
      simp only [payN, Function.update_of_ne (Ne.symm h3P), Function.update_self, hpoolB]
      omega
    rw [he, TL_payN (by simp [hK']) (by simp [hK']) _ hafter,
      if_neg (show spendA.feeRecipientAccount ≠ spendA.treeTokenAccount from h4P), add_zero,
      TL_payN (by simp [hK']) (by simp [hK']) _ (by show ext.val.natAbs ≤ (sB tokenA).lamports.val; rw [hpoolB]; omega),
      if_neg (show spendA.recipient ≠ spendA.treeTokenAccount from h3P), add_zero,
      mB, TL_moveN (by simp [hK']) (by simp [hK']) _ (by show 1 ≤ (sA spendA.signer).lamports.val; omega),
      mA, TL_moveN (by simp [hK']) (by simp [hK']) _ (by show 1 ≤ (s₂ spendA.signer).lamports.val; rw [hPs]; decide)]
  -- the account checks
  have hv : TransactAccountsValid toyD.toAddresses s₂ toyTx.toTxContext spendA spendProof.input_nullifiers.val[0]!
      spendProof.input_nullifiers.val[1]! tree₂ token config := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩, ⟨⟨?_, ?_⟩, ?_⟩,
      by simp [spendA, toyTx], rfl⟩
    · show (s₂ treeA).owner = _; rw [hT]
    · show (s₂ treeA).data = _; rw [hT]
    · rw [hTb]; rfl
    · obtain ⟨-, h1, h2⟩ := hz nf0W w01 w02 w03 w04 w05 w06; exact ⟨h1, h2⟩
    · obtain ⟨-, h1, h2⟩ := hz nf1W w11 w12 w13 w14 w15 w16; exact ⟨h1, h2⟩
    · exact (hz nf2W w21 w22 w23 w24 w25 w26).2.1
    · exact (hz nf3W w31 w32 w33 w34 w35 w36).2.1
    · show (s₂ tokenA).owner = _; rw [hK]
    · show (s₂ tokenA).data = _; rw [hK]
    · rw [hkb]; rfl
    · show (s₂ configA).owner = _; rw [hC]
    · show (s₂ configA).data = _; rw [hC]
    · rw [hcb]; rfl
  obtain ⟨events, hex⟩ := execTransact_ok_of (by show (s₂ treeA).data = _; rw [hT])
    (by show (s₂ tokenA).data = _; rw [hK]) (by show (s₂ configA).data = _; rw [hC]) hv rfl
    (by rw [hA, Option.bind_some, hB]) hh hTL
  exact ⟨_, events, hex⟩

/-! ## The whole toy execution -/

/-- The three steps (`initialize`, the deposit, the withdrawal, with either split) are accepted, and the withdrawal
    satisfies every hypothesis of `transact_connection` that is not about the execution. -/
theorem toy_spend_execution {ext : I64} {fee : U64} (hsplit : ToySplit ext fee) :
    ∃ (s₁ s₂ s₃ : State) (e₂ e₃ : List CommitmentData),
      step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, []) ∧
      step toyD s₁ toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) = .ok (s₂, e₂) ∧
      step toyD s₂ toyTx (.transact spendA spendProof ext fee emptySlice emptySlice) = .ok (s₃, e₃) ∧
      Initialized toyD s₁ ∧ (CryptoFacts toyD spendProof ∧ CircuitFacts toyD {spendProof}) ∧
      OutsideSpecDetail toyD toyRent s₂ toyTx spendA spendProof := by
  obtain ⟨s₁, tree, token, config, hinit, hT, hK, hC, hP, hO, hshape, hroots, hsubs, hT0, hTn, hTb, hTm,
    hkb, hcb, hdr, hwr, hmr⟩ := toy_init_ok
  obtain ⟨s₂, e₂, tree₂, hstep₂, hT2, hK2, hC2, hP2, hO2, p1, p2, t1, hap1, hap2⟩ :=
    toy_deposit_ok s₁ tree token config hT hK hC hP hO hshape hroots hsubs hT0 hTn hTb (hTm ▸ default_limit_ge2) hkb hcb hdr hwr hmr
  have hinitStep : step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, []) := by
    show (do let s' ← execInitialize toyD toyS0 toyTx toyInitA; pure (s', [])) = _
    rw [hinit]; rfl
  -- the deposit's two appends
  obtain ⟨-, hsh1, -, hn1, -, -, hb1⟩ := append_ok' toyCrypto toyHashesAgree _ tree t1 p1 hshape hap1
  obtain ⟨htree, hsh2, -, hn2, -, -, hb2⟩ := append_ok' toyCrypto toyHashesAgree _ t1 tree₂ p2 hsh1 hap2
  -- the tree after the deposit stores canonical roots and subtrees (`WellFormed`)
  have hrun₂ : Run toyD toyS0 [.program toyTx (.initialize toyInitA) [],
      .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂] s₂ :=
    .program hinitStep toyTx_rentPositive (.program hstep₂ toyTx_rentPositive (.nil _))
  have hpid : toyD.programId ≠ systemProgram := by unfold toyD; decide +kernel
  have wf₂ := wf_reachable toyGenesis hrun₂ hpid toyHashesAgree
  have hold₂ : HoldsTree toyD.programId s₂ treeA tree₂ := by unfold HoldsTree; rw [hT2]; exact ⟨rfl, rfl⟩
  obtain ⟨s₃, e₃, hstep₃⟩ := toy_spend_ok s₂ tree₂ t1 token config _ hT2 hK2 hC2 hP2 hO2 hsh2
    (wf₂.storedRoots _ _ hold₂) (wf₂.storedSubtrees _ _ hold₂) htree (by rw [hn2, hn1, hTn]; rfl)
    (by rw [hb2, hb1, hTb]) hkb hcb hdr hwr hmr hsplit
  obtain ⟨w01, w02, w03, w04, w05, w06, w11, w12, w13, w14, w15, w16, w0n1, -, -, -, -, -, -,
    -, -, -, -, -, -, p30, p31, p40, p41, p3a, p3b⟩ := spend_addr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, p3T, p3K, p3C, p4T, p4K, p4C,
    -, -, p4a, p4b, -, -⟩ := dep_addr
  have p31' : pk 3#u8 ≠ pk 1#u8 := pk_ne (by decide)
  have p41' : pk 4#u8 ≠ pk 1#u8 := pk_ne (by decide)
  refine ⟨s₁, s₂, s₃, e₂, e₃, hinitStep, hstep₂, hstep₃,
    ⟨⟨tree, by unfold HoldsTree; rw [show treeAddr toyD = treeA from rfl, hT]; exact ⟨rfl, rfl⟩⟩,
     ⟨token, by unfold HoldsTreeToken; rw [show poolAddr toyD = tokenA from rfl, hK]; exact ⟨rfl, rfl⟩⟩,
     ⟨config, by unfold HoldsGlobalConfig; rw [show configAddr toyD = configA from rfl, hC]; exact ⟨rfl, rfl⟩⟩⟩,
    ⟨⟨?_⟩, CircuitFacts.of_distinct ?_⟩, ⟨rfl, ?_, ?_⟩⟩
  · intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact absurd hxy w0n1
    · exact absurd hxy.symm w0n1
    · rfl
  · show two32 ≠ three32; decide +kernel
  · refine ⟨?_, ?_⟩
    · show (s₂ nf0W).lamports.val = 0
      rw [hO2 nf0W w01 w02 w03 w04 w05 w06]; unfold toyS0; decide +kernel
    · show (s₂ nf1W).lamports.val = 0
      rw [hO2 nf1W w11 w12 w13 w14 w15 w16]; unfold toyS0; decide +kernel
  · refine ⟨fun b h => ?_, fun b h => ?_, p30, p31, p40, p41⟩
    · rw [show s₂ spendA.recipient = toyS0 (pk 3#u8) from hO2 _ p3T p3K p3C p31' p3a p3b] at h
      unfold toyS0 at h; rw [if_neg p31'] at h; cases h
    · rw [show s₂ spendA.feeRecipientAccount = toyS0 (pk 4#u8) from hO2 _ p4T p4K p4C p41' p4a p4b] at h
      unfold toyS0 at h; rw [if_neg p41'] at h; cases h

/-- The three-event toy execution, split at any program step. -/
theorem toy_split3 {e₁ e₂ e₃ ev : Event} {pre post : List Event} (h : [e₁, e₂, e₃] = pre ++ ev :: post) :
    ev = e₁ ∨ ev = e₂ ∨ ev = e₃ := by
  rcases pre with _ | ⟨x, _ | ⟨y, _ | ⟨z, pre⟩⟩⟩
  · simp at h; exact Or.inl h.1.symm
  · simp at h; exact Or.inr (Or.inl h.2.1.symm)
  · simp at h; exact Or.inr (Or.inr h.2.2.1.symm)
  · simp at h

/-! ## Non-vacuity, with a real spend -/

/-- `transact_connection`'s hypotheses hold together in one toy deployment, for an accepted
    deposit and for an accepted withdrawal (a transaction that pays out of the pool). -/
theorem toy_transact_nonvacuous :
    ∃ (d : Deployment) (rent : Nat → U64) (s₀ : State)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      PairingLaws C.e ∧ Genesis d.programId s₀ ∧ DeploymentFacts d ∧ HashesAgree d.crypto ∧
      (∃ (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts) (proof : transact.Proof)
          (extAmount : I64) (fee : U64) (out1 out2 : Slice U8) (events : List CommitmentData),
        Run d s₀ evs s ∧ Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s' ∧
        extAmount.val > 0 ∧ SolanaFacts d tx ∧ CryptoFacts d proof ∧ CircuitFacts d {proof} ∧
        OutsideSpecDetail d rent s tx a proof) ∧
      (∃ (evs : List Event) (s s' : State) (tx : TxEnv) (a : TransactAccounts) (proof : transact.Proof)
          (extAmount : I64) (fee : U64) (out1 out2 : Slice U8) (events : List CommitmentData),
        Run d s₀ evs s ∧ Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s' ∧
        extAmount.val < 0 ∧ SolanaFacts d tx ∧ CryptoFacts d proof ∧ CircuitFacts d {proof} ∧
        OutsideSpecDetail d rent s tx a proof) := by
  obtain ⟨s₁, s₂, s₃, e₂, e₃, h1, h2, h3, -, crypto, outside⟩ := toy_spend_execution toySplit_one
  obtain ⟨s₁', s₂', e₂', h1', -, hpid, h2', -, solana, depCrypto, depOutside⟩ := toy_execution
  exact ⟨toyD, toyRent, toyS0, toyC, toyLaws, toyGenesis, toyDeploymentFacts, toyHashesAgree,
    ⟨_, s₁', s₂', toyTx, depA, depProof, 2#i64, 0#u64, emptySlice, emptySlice, e₂',
      .program h1' toyTx_rentPositive (.nil _), .program h2' toyTx_rentPositive (.nil _), by simp, solana, depCrypto.1, depCrypto.2, depOutside⟩,
    ⟨_, s₂, s₃, toyTx, spendA, spendProof, wdExt, 1#u64, emptySlice, emptySlice, e₃,
      .program h1 toyTx_rentPositive (.program h2 toyTx_rentPositive (.nil _)), .program h3 toyTx_rentPositive (.nil _), by rw [wdExt_val]; decide, solana, crypto.1, crypto.2, outside⟩⟩

/-- **The hypotheses of `run_connection` and of the goals about runs hold together, with a real
    spend.** The execution `initialize`, deposit, withdrawal satisfies every hypothesis of
    `run_connection`, initializes the pool, and has two transactions. `wit` are circuit
    witnesses for both (so for every spec run of the execution, whose transactions `IsRunOf`
    fixes to `runTxs evs`), and in them the withdrawal (transaction 1) spends a non-zero note:
    the one at leaf 0, which the deposit created. -/
theorem toy_spend_nonvacuous :
    ∃ (d : Deployment) (s₀ s : State) (evs : List Event) (states : List State)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit),
      PairingLaws C.e ∧ Genesis d.programId s₀ ∧ ExecutionPath d s₀ evs states s ∧
      DeploymentFacts d ∧
      HashesAgree d.crypto ∧ ExecutionAssumptions d s₀ evs ∧
      ExecutionOutsideSpecDetail d toyRent s₀ evs ∧ Initialized d s ∧
      (runTxs evs).length = 2 ∧
      ∃ wit : ℕ → LeanSpec.Witness,
        (∀ j (h : j < (runTxs evs).length), LeanSpec.RelationS (runTxs evs)[j].pubInputs (wit j)) ∧
        (wit 1).inAmt 0 ≠ 0 ∧ LeanSpec.openedPos wit 1 0 = 0 ∧
        (wit 1).inNote 0 = LeanSpec.leafNote wit 0 := by
  obtain ⟨s₁, s₂, s₃, e₂, e₃, h1, h2, h3, hi₁, crypto, -⟩ := toy_spend_execution toySplit_one
  obtain ⟨-, -, -, -, -, -, -, -, solana, depCrypto, -⟩ := toy_execution
  have hpid : toyD.programId ≠ systemProgram := by unfold toyD; decide +kernel
  have wf₁ := wf_reachable toyGenesis (.program h1 toyTx_rentPositive (.nil _)) hpid toyHashesAgree
  have wf₂ := wf_reachable toyGenesis (.program h1 toyTx_rentPositive (.program h2 toyTx_rentPositive (.nil _))) hpid toyHashesAgree
  have hi₃ := transact_initialized wf₂ (transact_initialized wf₁ hi₁ h2) h3
  have htxs : runTxs [Event.program toyTx (.initialize toyInitA) [],
      .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂,
      .program toyTx (.transact spendA spendProof wdExt 1#u64 emptySlice emptySlice) e₃] =
      [toInputs toyTx.signers depA depProof 2#i64 0#u64 emptySlice emptySlice,
        toInputs toyTx.signers spendA spendProof wdExt 1#u64 emptySlice emptySlice] := by
    simp [runTxs, stepTxs]
  refine ⟨toyD, toyS0, s₃, _, _, toyC, toyLaws, toyGenesis, .program h1 toyTx_rentPositive (.program h2 toyTx_rentPositive (.program h3 toyTx_rentPositive (.nil _))),
    toyDeploymentFacts, toyHashesAgree, ⟨toy_fixed_addresses, ?_⟩, ⟨?_⟩, hi₃, by rw [htxs]; rfl,
    fun j => if j = 0 then depWit else spendWit, ?_, ?_, rfl, rfl⟩
  · intro pre post s tx ix em hsplit _
    rcases toy_split3 hsplit with hev | hev | hev <;> cases hev
    · trivial
    · exact ⟨solana, depCrypto⟩
    · exact ⟨solana, crypto⟩
  · intro pre post s tx ix em hsplit _
    rcases toy_split3 hsplit with hev | hev | hev <;> cases hev <;> rfl
  · intro j hj
    rw [List.getElem_of_eq htxs hj]
    have hj2 : j < 2 := by rw [htxs] at hj; simpa using hj
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · exact dep_relation
    · exact spend_relation
  · show spendWit.inAmt 0 ≠ 0
    simp only [spendWit, Matrix.cons_val_zero]; decide

end Connection.Toy
