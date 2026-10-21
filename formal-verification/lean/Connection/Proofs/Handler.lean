import Connection.Proofs.Verifier
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: the extracted `transact` handler with the model's Solana runtime

NOT FOR REVIEW. -/

namespace Connection
open zkcash_core

/-- A `program_err` rejection never returns `Ok`. -/
theorem progErr_ne {R : Type} (e : error.ErrorCode) (rt rt' : R) (t t' : merkle_tree.MerkleTreeAccount)
    (ap : transact.Appended) :
    (do let r ← transact.program_err transact.Appended e; ok (r, rt, t)) ≠ ok (.Ok ap, rt', t') := by
  simp [transact.program_err]

theorem ite_pos' {α : Type} {c : Prop} [Decidable c] {x y r : α}
    (h : (if c then x else y) = r) (hc : c) : x = r := by rw [if_pos hc] at h; exact h

theorem ite_neg' {α : Type} {c : Prop} [Decidable c] {x y r : α}
    (h : (if c then x else y) = r) (hc : ¬ c) : y = r := by rw [if_neg hc] at h; exact h

/-- Close a branch that returns a rejection (`Err`), never `Ok`. -/
syntax "reject " ident : tactic
macro_rules
  | `(tactic| reject $h) => `(tactic| (
    first
    | exact absurd $h:ident (progErr_ne _ _ _ _ _ _)
    | (have hrej := Result.ok_injective $h:ident; simp at hrej)))

/-- Peel the handler's final two appends and the index computation; leaves `ha1 ha2` for the
    two appends and replaces `env'`/`tree'` by what the code returned. -/
syntax "appends_tail " ident ident ident ident ident : tactic
macro_rules
  | `(tactic| appends_tail $h $hi0 $ha1 $hi1 $ha2) => `(tactic| (
    obtain ⟨_, $hi0:ident, $h:ident⟩ := bindOk $h:ident
    obtain ⟨⟨r2, ta1⟩, $ha1:ident, $h:ident⟩ := bindOk $h:ident
    cases r2; rotate_left; exact absurd $h:ident (progErr_ne _ _ _ _ _ _)
    obtain ⟨_, $hi1:ident, $h:ident⟩ := bindOk $h:ident
    obtain ⟨⟨r3, ta2⟩, $ha2:ident, $h:ident⟩ := bindOk $h:ident
    cases r3; rotate_left; exact absurd $h:ident (progErr_ne _ _ _ _ _ _)
    obtain ⟨o1, _, $h:ident⟩ := bindOk $h:ident
    cases o1; exact absurd $h:ident (progErr_ne _ _ _ _ _ _)
    have hfin := Result.ok_injective $h:ident
    simp only [Prod.mk.injEq] at hfin
    obtain ⟨-, hfin1, hfin2⟩ := hfin
    subst hfin1; subst hfin2))

/-- Move `x` lamports from `src` to `dst` (the spec's `moveLamports`, on code addresses). -/
def moveN (b : Pubkey → ℕ) (src dst : Pubkey) (x : ℕ) : Pubkey → ℕ :=
  let b' := Function.update b src (b src - x)
  Function.update b' dst (b' dst + x)

theorem setBalance_vals (b : Pubkey → U64) (k : Pubkey) (v : U64) :
    (fun k' => (setBalance b k v k').val) = Function.update (fun k' => (b k').val) k v.val := by
  funext k'
  simp only [setBalance, Function.update]
  by_cases h : k' = k <;> simp [h]

theorem u64_pos {x : U64} (h : x > 0#u64) : x.val > 0 := by scalar_tac
theorem u64_not_pos {x : U64} (h : ¬ x > 0#u64) : x.val = 0 := by scalar_tac
theorem i64_pos {x : I64} (h : x > 0#i64) : x.val > 0 := by scalar_tac
theorem i64_not_pos {x : I64} (h : ¬ x > 0#i64) : x.val ≤ 0 := by scalar_tac
theorem i64_neg {x : I64} (h : x < 0#i64) : x.val < 0 := by scalar_tac
theorem i64_not_neg {x : I64} (h : ¬ x < 0#i64) : 0 ≤ x.val := by scalar_tac
theorem i64_ge0 {x : I64} (h : x.val ≥ 0) : x ≥ 0#i64 := by scalar_tac
theorem i64_not_ge0 {x : I64} (h : x.val < 0) : ¬ x ≥ 0#i64 := by scalar_tac
theorem i64_bounds (x : I64) : -2 ^ 63 ≤ x.val ∧ x.val < 2 ^ 63 := by constructor <;> scalar_tac

theorem checked_sub_some {x y z : U64} (h : U64.checked_sub x y = some z) : z.val = x.val - y.val := by
  have hs := U64.checked_sub_bv_spec x y; rw [h] at hs; exact hs.2.1
theorem checked_add_some {x y z : U64} (h : U64.checked_add x y = some z) : z.val = x.val + y.val := by
  have hs := U64.checked_add_bv_spec x y; rw [h] at hs; exact hs.2.1

theorem i64_neg_ok (x : I64) (hx : x.val ≠ -9223372036854775808) :
    ∃ y, IScalar.neg x = ok y ∧ y.val = -x.val := by
  have := IScalar.neg_step x (by intro hm; apply hx; rw [hm]; simp [I64.min_eq])
  cases hr : IScalar.neg x <;> simp_all

theorem idx2 (x : Std.Array (Std.Array U8 32#usize) 2#usize) (k : Usize) (v : Std.Array U8 32#usize)
    (hk : k.val < 2) (hv : x.index_usize k = ok v) : v = x.val[k.val]! := by
  obtain ⟨v', hv', hvv⟩ := (WP.spec_equiv_exists _ _).mp (Std.Array.index_usize_spec x k (by simp; omega))
  rw [hv'] at hv; obtain rfl := Result.ok_injective hv
  rw [hvv, getElem!_pos _ _ (by simp; omega)]

theorem stb_spec {acc : State} {bal : Pubkey → U64} {src dst : Pubkey} {amt : U64}
    {b : Pubkey → U64} (h : systemTransferBalances acc bal src dst amt = some b) :
    (acc src).owner = systemProgram ∧ (acc src).data.isEmpty ∧ amt.val ≤ (bal src).val ∧
      (fun k => (b k).val) = moveN (fun k => (bal k).val) src dst amt.val := by
  unfold systemTransferBalances at h
  split at h
  swap; · simp at h
  rename_i h1
  simp only at h
  split at h
  swap; · simp at h
  rename_i h2
  obtain ⟨ho, hd, hle⟩ := h1
  simp only [Option.some.injEq] at h
  subst h
  refine ⟨ho, hd, hle, ?_⟩
  have hsub : (⟨(bal src).bv - amt.bv⟩ : U64).val = (bal src).val - amt.val := by
    show ((bal src).bv - amt.bv).toNat = _
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, U64.bv_toNat, U64.bv_toNat]; exact hle),
      U64.bv_toNat, U64.bv_toNat]
  have hv1 : (fun k => (setBalance bal src ⟨(bal src).bv - amt.bv⟩ k).val)
      = Function.update (fun k => (bal k).val) src ((bal src).val - amt.val) := by
    rw [setBalance_vals, hsub]
  have hadd : (⟨(setBalance bal src ⟨(bal src).bv - amt.bv⟩ dst).bv + amt.bv⟩ : U64).val
      = (setBalance bal src ⟨(bal src).bv - amt.bv⟩ dst).val + amt.val := by
    show ((setBalance bal src ⟨(bal src).bv - amt.bv⟩ dst).bv + amt.bv).toNat = _
    rw [BitVec.toNat_add_of_lt, U64.bv_toNat, U64.bv_toNat]
    rw [U64.bv_toNat, U64.bv_toNat]; have := h2; scalar_tac
  rw [setBalance_vals, hv1, hadd, show (setBalance bal src ⟨(bal src).bv - amt.bv⟩ dst).val
    = Function.update (fun k => (bal k).val) src ((bal src).val - amt.val) dst from congrFun hv1 dst]
  rfl

theorem setLamports_vals (e : SolEnv) (k : Pubkey) (v : U64) :
    (fun k' => ((e.setLamports k v).balances k').val) = Function.update (fun k' => (e.balances k').val) k v.val := by
  funext k'
  simp only [SolEnv.setLamports, setBalance, Function.update]
  by_cases h : k' = k <;> simp [h]

theorem moveN_zero (b : Pubkey → ℕ) (src dst : Pubkey) : moveN b src dst 0 = b := by
  unfold moveN; simp

/-- A payment as the code makes it: read both balances, then write both. Differs from `moveN`
    only when `src = dst`, where it creates `x` lamports. -/
def payN (b : Pubkey → ℕ) (src dst : Pubkey) (x : ℕ) : Pubkey → ℕ :=
  Function.update (Function.update b src (b src - x)) dst (b dst + x)

theorem payN_zero (b : Pubkey → ℕ) (src dst : Pubkey) : payN b src dst 0 = b := by
  unfold payN; simp

theorem moveN_eq_updates (W : Pubkey → ℕ) (p t : Pubkey) (hne : t ≠ p) (x : ℕ) :
    moveN W p t x = Function.update (Function.update W p (W p - x)) t (W t + x) := by
  simp only [moveN, Function.update_of_ne hne]

/-- What a successful run of the handler guarantees. -/
structure HandlerOk (c : Crypto) (env : SolEnv) (tree : merkle_tree.MerkleTreeAccount)
    (config : admin.GlobalConfig) (proof : transact.Proof) (ext : I64) (fee : U64)
    (recipient feeRecipient : Pubkey) (out1 out2 : Slice U8)
    (env' : SolEnv) (tree' : merkle_tree.MerkleTreeAccount) : Prop where
  root : merkle_tree.is_known_root tree proof.root = ok true
  extHash : ∃ hsh, ext_data.calculate_complete_ext_data_hash c.sha256 recipient ext out1 out2 fee
      feeRecipient transact.SOL_ADDRESS = ok (some hsh) ∧ (leNat hsh : Fr) = (beNat proof.ext_data_hash : Fr)
  pubAmt : utils.check_public_amount arkFr ext fee proof.public_amount = ok true
  feeOk : utils.validate_fee ext fee config.deposit_fee_rate config.withdrawal_fee_rate
      config.fee_error_margin = ok (.Ok ())
  verify : c.proofVerifier.verify proof = ok true
  depositLimit : ext.val > 0 → ext.val ≤ tree.max_deposit_amount.val
  appends : ∃ p1 p2 t1, merkle_tree.append c.hasher proof.output_commitments.val[0]! tree = ok (.Ok p1, t1) ∧
      merkle_tree.append c.hasher proof.output_commitments.val[1]! t1 = ok (.Ok p2, tree')
  sameEnv : env'.accounts = env.accounts ∧ env'.signer = env.signer ∧ env'.treeToken = env.treeToken ∧
      env'.recipient = env.recipient ∧ env'.feeRecipient = env.feeRecipient
  rent : ∃ v : U64, env.rentExemptMinimum = some v ∧
    (ext.val > 0 →
      (env.accounts env.signer).owner = systemProgram ∧ (env.accounts env.signer).data.isEmpty ∧
      ext.val ≤ (env.balances env.signer).val ∧
      (fee.val > 0 → moveN (fun k => (env.balances k).val) env.signer env.treeToken ext.val.natAbs env.treeToken
          ≥ fee.val + v.val) ∧
      (fun k => (env'.balances k).val) = payN (moveN (fun k => (env.balances k).val) env.signer
          env.treeToken ext.val.natAbs) env.treeToken env.feeRecipient fee.val) ∧
    (ext.val < 0 →
      (env.balances env.treeToken).val ≥ ext.val.natAbs + fee.val + v.val ∧
      (fun k => (env'.balances k).val) = payN (payN (fun k => (env.balances k).val) env.treeToken
          env.recipient ext.val.natAbs) env.treeToken env.feeRecipient fee.val)

/-- **The handler, when it returns `Ok`.** The balance equations are exactly the code's
    read-before-write updates (`payN`), for any accounts, aliased or not. -/
theorem handler_ok (c : Crypto) (env : SolEnv) (tree : merkle_tree.MerkleTreeAccount)
    (config : admin.GlobalConfig) (proof : transact.Proof) (ext : I64) (fee : U64)
    (recipient feeRecipient : Pubkey) (out1 out2 : Slice U8) (appended : transact.Appended)
    (env' : SolEnv) (tree' : merkle_tree.MerkleTreeAccount)
    (h : transact.transact c.hasher arkFr c.sha256 c.proofVerifier solRuntime env tree config proof
      ext fee recipient feeRecipient out1 out2 = ok (.Ok appended, env', tree')) :
    HandlerOk c env tree config proof ext fee recipient feeRecipient out1 out2 env' tree' := by
  unfold transact.transact at h
  obtain ⟨b, hb, h⟩ := bindOk h
  cases b
  · rw [if_neg Bool.false_ne_true] at h; reject h
  rw [if_pos rfl] at h
  obtain ⟨o, ho, h⟩ := bindOk h
  cases o
  · reject h
  rename_i hsh
  obtain ⟨t, ht, h⟩ := bindOk h
  obtain ⟨t1, ht1, h⟩ := bindOk h
  obtain ⟨b1, hb1, h⟩ := bindOk h
  cases b1
  · rw [if_neg Bool.false_ne_true] at h; reject h
  rw [if_pos rfl] at h
  obtain ⟨b2, hb2, h⟩ := bindOk h
  cases b2
  · rw [if_neg Bool.false_ne_true] at h; reject h
  rw [if_pos rfl] at h
  obtain ⟨r, hr, h⟩ := bindOk h
  cases r
  rotate_left; · reject h
  rename_i u
  obtain ⟨b3, hb3, h⟩ := bindOk h
  cases b3
  · rw [if_neg Bool.false_ne_true] at h; reject h
  rw [if_pos rfl] at h
  obtain ⟨⟨r1, rt1⟩, hr1, h⟩ := bindOk h
  -- the rent
  obtain ⟨v, hv, hrt1, hr1v⟩ : ∃ v, env.rentExemptMinimum = some v ∧ rt1 = env ∧ r1 = .Ok v := by
    cases hre : env.rentExemptMinimum with
    | none =>
      have := Result.ok_injective hr1
      simp [hre] at this
      rw [← this.1] at h; reject h
    | some v' =>
      have := Result.ok_injective hr1
      simp [hre] at this
      exact ⟨v', rfl, this.2.symm, this.1.symm⟩
  subst hr1v
  rw [hrt1] at h
  -- the checks
  have hext : (leNat hsh : Fr) = (beNat proof.ext_data_hash : Fr) := by
    have e1 := Result.ok_injective ht; have e2 := Result.ok_injective ht1
    have e3 := Result.ok_injective hb1
    rw [← e1, ← e2] at e3
    simpa using e3.symm
  have hrfee : utils.validate_fee ext fee config.deposit_fee_rate config.withdrawal_fee_rate
      config.fee_error_margin = ok (.Ok ()) := hr
  by_cases hpos : ext > 0#i64
  · -- DEPOSIT
    have hposv : ext.val > 0 := i64_pos hpos
    have h := ite_pos' h hpos
    obtain ⟨dep, hdep, h⟩ := bindOk h
    obtain rfl : IScalar.hcast .U64 ext = dep := Result.ok_injective hdep
    have hhi : ext.val < 2 ^ 63 := (i64_bounds ext).2
    have hdepv : (IScalar.hcast .U64 ext).val = ext.val.natAbs := by
      rw [IScalar.hcast_val_eq, show UScalarTy.U64.numBits = 64 from rfl,
        Int.emod_eq_of_lt (by omega) (by omega)]; omega
    by_cases hlim : IScalar.hcast .U64 ext ≤ tree.max_deposit_amount
    swap; · have h := ite_neg' h hlim; reject h
    have h := ite_pos' h hlim
    obtain ⟨i, hi, h⟩ := bindOk h
    obtain rfl : IScalar.hcast .U64 ext = i := Result.ok_injective hi
    obtain ⟨⟨r2, rt2⟩, htr, h⟩ := bindOk h
    cases hst : systemTransferBalances env.accounts env.balances env.signer env.treeToken (IScalar.hcast .U64 ext) with
    | none =>
      have e := Result.ok_injective htr
      unfold SolEnv.systemTransfer at e
      rw [hst] at e
      obtain ⟨hr2, -⟩ := Prod.mk.inj e.symm
      rw [hr2] at h
      reject h
    | some b1 =>
    have e := Result.ok_injective htr
    unfold SolEnv.systemTransfer at e
    rw [hst] at e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e.symm
    obtain ⟨hso, hsd, hsle, hsb⟩ := stb_spec hst
    rw [hdepv] at hsle hsb
    have hsleZ : ext.val ≤ ((env.balances env.signer).val : ℤ) := by
      rw [← Int.natAbs_of_nonneg (le_of_lt hposv)]; exact_mod_cast hsle
    by_cases hf : fee > 0#u64
    · have hfv : fee.val > 0 := u64_pos hf
      have h := ite_pos' h hf
      have hge0 : ext ≥ 0#i64 := i64_ge0 (by omega)
      have h := ite_pos' h hge0
      obtain ⟨o1, ho1, h⟩ := bindOk h
      have ho1' : fee.checked_add v = o1 := Result.ok_injective ho1
      cases o1
      · reject h
      rename_i v1
      have hv1 : v1.val = fee.val + v.val := by
        have hs := U64.checked_add_bv_spec fee v; rw [ho1'] at hs; exact hs.2.1
      obtain ⟨i1, hi1, h⟩ := bindOk h
      obtain rfl : b1 env.treeToken = i1 := Result.ok_injective hi1
      by_cases hge : b1 env.treeToken ≥ v1
      swap; · have h := ite_neg' h hge; reject h
      have h := ite_pos' h hge
      obtain ⟨frb, hfrb, h⟩ := bindOk h
      obtain rfl : b1 env.feeRecipient = frb := Result.ok_injective hfrb
      obtain ⟨o2, ho2, h⟩ := bindOk h
      have ho2' : (b1 env.treeToken).checked_sub fee = o2 := Result.ok_injective ho2
      cases o2
      · reject h
      rename_i v2
      have hv2 : v2.val = (b1 env.treeToken).val - fee.val := by
        have hs := U64.checked_sub_bv_spec (b1 env.treeToken) fee; rw [ho2'] at hs; exact hs.2.1
      obtain ⟨o3, ho3, h⟩ := bindOk h
      have ho3' : (b1 env.feeRecipient).checked_add fee = o3 := Result.ok_injective ho3
      cases o3
      · reject h
      rename_i v3
      have hv3 : v3.val = (b1 env.feeRecipient).val + fee.val := by
        have hs := U64.checked_add_bv_spec (b1 env.feeRecipient) fee; rw [ho3'] at hs; exact hs.2.1
      obtain ⟨⟨r3, rt3⟩, hs3, h⟩ := bindOk h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hs3).symm
      obtain ⟨⟨r4, rt4⟩, hs4, h⟩ := bindOk h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hs4).symm
      appends_tail h hi0 hap1 hi1 hap2
      refine { root := hb, extHash := ⟨hsh, ho, hext⟩, pubAmt := hb2, feeOk := hrfee, verify := hb3,
               depositLimit := fun _ => ?_,
               appends := ⟨_, _, _, (idx2 _ _ _ (by decide) hi0) ▸ hap1, (idx2 _ _ _ (by decide) hi1) ▸ hap2⟩,
               sameEnv := ⟨rfl, rfl, rfl, rfl, rfl⟩, rent := ⟨v, hv, fun _ => ⟨hso, hsd, hsleZ, fun _ => ?_, ?_⟩,
                 fun hn => absurd hn (by omega)⟩ }
      · have : (IScalar.hcast .U64 ext).val ≤ tree.max_deposit_amount.val := hlim
        omega
      · rw [← hsb]
        have : (b1 env.treeToken).val ≥ v1.val := hge
        show (b1 env.treeToken).val ≥ fee.val + v.val
        omega
      · rw [setLamports_vals, setLamports_vals, ← hsb, hv2, hv3]; rfl
    · have h := ite_neg' h hf
      have hf0 : fee.val = 0 := u64_not_pos hf
      appends_tail h hi0 hap1 hi1 hap2
      refine { root := hb, extHash := ⟨hsh, ho, hext⟩, pubAmt := hb2, feeOk := hrfee, verify := hb3,
               depositLimit := fun _ => ?_,
               appends := ⟨_, _, _, (idx2 _ _ _ (by decide) hi0) ▸ hap1, (idx2 _ _ _ (by decide) hi1) ▸ hap2⟩,
               sameEnv := ⟨rfl, rfl, rfl, rfl, rfl⟩, rent := ⟨v, hv, fun _ => ⟨hso, hsd, hsleZ,
                 fun hfp => absurd hfp (by omega), ?_⟩, fun hn => absurd hn (by omega)⟩ }
      · have : (IScalar.hcast .U64 ext).val ≤ tree.max_deposit_amount.val := hlim
        omega
      · rw [hf0, payN_zero, ← hsb]
  · have h := ite_neg' h hpos
    have hpub : LeanSpec.pubAmtConsistent ext.val fee.val (toF proof.public_amount) ∧
        LeanSpec.amountsInRange ext.val fee.val ∧ ext.val ≠ 0 := by
      have := (checkPublicAmount_eq ext fee proof.public_amount).symm.trans hb2
      simpa using this
    by_cases hneg : ext < 0#i64
    swap
    · -- ZERO: excluded by the public-amount check
      have h0 : ext.val = 0 := by have := i64_not_pos hpos; have := i64_not_neg hneg; omega
      exfalso
      exact hpub.2.2 h0
    -- WITHDRAWAL
    have hnegv : ext.val < 0 := i64_neg hneg
    have hlo := (i64_bounds ext).1
    have h := ite_pos' h hneg
    obtain ⟨y, hy, hyv⟩ := i64_neg_ok ext (by have := hpub.2.1.1; omega)
    obtain ⟨o1, ho1, h⟩ := bindOk h
    have ho1' : o1 = some y := by
      have := Result.ok_injective ho1
      simp only [core.num.I64.checked_neg, hy, Option.ofResult, Result.match.ok] at this
      exact this.symm
    subst ho1'
    have hy0 : ¬ y < 0#i64 := by intro hc; have := i64_neg hc; omega
    have h := ite_neg' h hy0
    obtain ⟨absv, habs, h⟩ := bindOk h
    obtain rfl : IScalar.hcast .U64 y = absv := Result.ok_injective habs
    have habsv : (IScalar.hcast .U64 y).val = ext.val.natAbs := by
      rw [IScalar.hcast_val_eq, hyv, show UScalarTy.U64.numBits = 64 from rfl,
        Int.emod_eq_of_lt (by omega) (by omega)]; omega
    obtain ⟨o2, ho2, h⟩ := bindOk h
    have ho2' : U64.checked_add (IScalar.hcast .U64 y) fee = o2 := Result.ok_injective ho2
    cases o2
    · reject h
    rename_i v2
    have hv2 : v2.val = ext.val.natAbs + fee.val := by
      have hs := U64.checked_add_bv_spec (IScalar.hcast .U64 y) fee; rw [ho2'] at hs; rw [hs.2.1, habsv]
    obtain ⟨o3, ho3, h⟩ := bindOk h
    have ho3' : v2.checked_add v = o3 := Result.ok_injective ho3
    cases o3
    · reject h
    rename_i v3
    have hv3 : v3.val = v2.val + v.val := by
      have hs := U64.checked_add_bv_spec v2 v; rw [ho3'] at hs; exact hs.2.1
    obtain ⟨i, hi, h⟩ := bindOk h
    obtain rfl : env.balances env.treeToken = i := Result.ok_injective hi
    by_cases hge : env.balances env.treeToken ≥ v3
    swap; · have h := ite_neg' h hge; reject h
    have h := ite_pos' h hge
    obtain ⟨rb, hrb, h⟩ := bindOk h
    obtain rfl : env.balances env.recipient = rb := Result.ok_injective hrb
    obtain ⟨o4, ho4, h⟩ := bindOk h
    have ho4' : U64.checked_sub (env.balances env.treeToken) (IScalar.hcast .U64 y) = o4 := Result.ok_injective ho4
    cases o4
    · reject h
    rename_i v4
    have hv4 : v4.val = (env.balances env.treeToken).val - ext.val.natAbs := by
      have hs := U64.checked_sub_bv_spec (env.balances env.treeToken) (IScalar.hcast .U64 y)
      rw [ho4'] at hs; rw [hs.2.1, habsv]
    obtain ⟨o5, ho5, h⟩ := bindOk h
    have ho5' : U64.checked_add (env.balances env.recipient) (IScalar.hcast .U64 y) = o5 := Result.ok_injective ho5
    cases o5
    · reject h
    rename_i v5
    have hv5 : v5.val = (env.balances env.recipient).val + ext.val.natAbs := by
      have hs := U64.checked_add_bv_spec (env.balances env.recipient) (IScalar.hcast .U64 y)
      rw [ho5'] at hs; rw [hs.2.1, habsv]
    obtain ⟨⟨r3, rt3⟩, hs3, h⟩ := bindOk h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hs3).symm
    obtain ⟨⟨r4, rt4⟩, hs4, h⟩ := bindOk h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hs4).symm
    -- the balances after paying the recipient
    have hW : (fun k => (((env.setLamports env.treeToken v4).setLamports env.recipient v5).balances k).val)
        = payN (fun k => (env.balances k).val) env.treeToken env.recipient ext.val.natAbs := by
      rw [setLamports_vals, setLamports_vals, hv4, hv5]; rfl
    have hpoolv : (env.balances env.treeToken).val ≥ ext.val.natAbs + fee.val + v.val := by
      have : (env.balances env.treeToken).val ≥ v3.val := hge
      omega
    by_cases hf : fee > 0#u64
    · have h := ite_pos' h hf
      have hnge : ¬ ext ≥ 0#i64 := i64_not_ge0 hnegv
      have h := ite_neg' h hnge
      obtain ⟨ttb, httb, h⟩ := bindOk h
      obtain rfl := (Result.ok_injective httb)
      obtain ⟨frb, hfrb, h⟩ := bindOk h
      obtain rfl := (Result.ok_injective hfrb)
      obtain ⟨o6, ho6, h⟩ := bindOk h
      have ho6' := Result.ok_injective ho6
      cases o6
      · reject h
      rename_i v6
      obtain ⟨o7, ho7, h⟩ := bindOk h
      have ho7' := Result.ok_injective ho7
      cases o7
      · reject h
      rename_i v7
      obtain ⟨⟨r5, rt5⟩, hs5, h⟩ := bindOk h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hs5).symm
      obtain ⟨⟨r6, rt6⟩, hs6, h⟩ := bindOk h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Result.ok_injective hs6).symm
      have hv6 := checked_sub_some ho6'
      have hv7 := checked_add_some ho7'
      appends_tail h hi0 hap1 hi1 hap2
      refine { root := hb, extHash := ⟨hsh, ho, hext⟩, pubAmt := hb2, feeOk := hrfee, verify := hb3,
               depositLimit := fun hp => absurd hp (by omega),
               appends := ⟨_, _, _, (idx2 _ _ _ (by decide) hi0) ▸ hap1, (idx2 _ _ _ (by decide) hi1) ▸ hap2⟩,
               sameEnv := ⟨rfl, rfl, rfl, rfl, rfl⟩,
               rent := ⟨v, hv, fun hp => absurd hp (by omega), fun _ => ⟨hpoolv, ?_⟩⟩ }
      rw [setLamports_vals, setLamports_vals, ← hW, hv6, hv7]
      rfl
    · have h := ite_neg' h hf
      have hf0 : fee.val = 0 := u64_not_pos hf
      appends_tail h hi0 hap1 hi1 hap2
      refine { root := hb, extHash := ⟨hsh, ho, hext⟩, pubAmt := hb2, feeOk := hrfee, verify := hb3,
               depositLimit := fun hp => absurd hp (by omega),
               appends := ⟨_, _, _, (idx2 _ _ _ (by decide) hi0) ▸ hap1, (idx2 _ _ _ (by decide) hi1) ▸ hap2⟩,
               sameEnv := ⟨rfl, rfl, rfl, rfl, rfl⟩,
               rent := ⟨v, hv, fun hp => absurd hp (by omega), fun _ => ⟨hpoolv, ?_⟩⟩ }
      rw [hf0, payN_zero, ← hW]
      rfl

end Connection
