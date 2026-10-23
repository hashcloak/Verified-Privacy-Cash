import Connection.Proofs.Checks
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: the external data serialization and hash

NOT FOR REVIEW: the statements are restated in `Connection/ConnectionTheorems.lean`. -/

namespace Connection
open zkcash_core

private theorem drop_cons_getElem {α} (l : List α) (i : ℕ) (h : i < l.length) :
    l.drop i = l[i] :: l.drop (i + 1) := (List.drop_eq_getElem_cons h)

/-- `push_bytes` from index `i` appends the rest of `bytes`. -/
theorem pushBytesLoop_spec (out : alloc.vec.Vec U8) (bytes : Slice U8) (i : Usize)
    (hi : i.val ≤ bytes.length) (hcap : out.val.length + (bytes.length - i.val) ≤ Usize.max) :
    ext_data.push_bytes_loop out bytes i ⦃ r => r.val = out.val ++ bytes.val.drop i.val ⦄ := by
  unfold ext_data.push_bytes_loop
  apply loop.spec_decr_nat (fun (x : alloc.vec.Vec U8 × Usize) => bytes.length - x.2.val)
    (fun x => x.2.val ≤ bytes.length ∧ x.1.val.length + (bytes.length - x.2.val) ≤ Usize.max ∧
      x.1.val ++ bytes.val.drop x.2.val = out.val ++ bytes.val.drop i.val)
  · rintro ⟨cur, j⟩ ⟨hj, hc, heq⟩
    dsimp only at hj hc heq ⊢
    unfold ext_data.push_bytes_loop.body
    simp only
    split
    · rename_i hlt
      step*
      have hjl : j.val < bytes.length := by scalar_tac
      have hc' : cur.val.length + (bytes.val.length - j.val) ≤ Usize.max := hc
      refine ⟨by scalar_tac, by simp [out1_post, i3_post]; omega, ?_, by scalar_tac⟩
      rw [← heq, out1_post, drop_cons_getElem bytes.val j.val hjl, i3_post, i2_post]
      simp
    · simp only [WP.spec_ok]
      have : j.val = bytes.length := by scalar_tac
      rw [← heq, this]; simp
  · exact ⟨hi, hcap, rfl⟩

/-- The little-endian bytes `k₀ … 7` of `n`, as the spec writes them (`natToBytesLE`). -/
private def leBytesFrom (n : ℕ) (k₀ w : ℕ) : LeanSpec.Bytes :=
  ((List.range w).drop k₀).map (fun k => BitVec.ofNat 8 (n >>> (8 * k)))

private theorem leBytesFrom_succ (n k w : ℕ) (h : k < w) :
    leBytesFrom n k w = BitVec.ofNat 8 (n >>> (8 * k)) :: leBytesFrom n (k + 1) w := by
  simp only [leBytesFrom]
  rw [List.drop_eq_getElem_cons (by simpa using h)]
  simp

private theorem leBytesFrom_end (n w : ℕ) : leBytesFrom n w w = [] := by
  simp [leBytesFrom]

private theorem cast_u8_bv {ty : UScalarTy} (y : UScalar ty) :
    U8.bv (UScalar.cast .U8 y) = BitVec.ofNat 8 y.val := by
  apply BitVec.eq_of_toNat_eq
  rw [U8.bv_toNat, UScalar.cast_val_eq, BitVec.toNat_ofNat]; rfl

theorem pushU64Loop_spec (out : alloc.vec.Vec U8) (x : U64) (i : I32)
    (h0 : 0 ≤ i.val) (h8 : i.val ≤ 8) (hcap : out.val.length + 8 ≤ Usize.max) :
    ext_data.push_u64_le_loop out x i ⦃ r =>
      toBytes r.val = toBytes out.val ++ leBytesFrom x.val i.val.toNat 8 ⦄ := by
  unfold ext_data.push_u64_le_loop
  apply loop.spec_decr_nat (fun (y : alloc.vec.Vec U8 × I32) => 8 - y.2.val.toNat)
    (fun y => 0 ≤ y.2.val ∧ y.2.val ≤ 8 ∧ y.1.val.length + (8 - y.2.val.toNat) ≤ out.val.length + 8 ∧
      toBytes y.1.val ++ leBytesFrom x.val y.2.val.toNat 8 = toBytes out.val ++ leBytesFrom x.val i.val.toNat 8)
  · rintro ⟨cur, j⟩ ⟨hj0, hj8, hc, heq⟩
    dsimp only at hj0 hj8 hc heq ⊢
    unfold ext_data.push_u64_le_loop.body
    split
    · rename_i hlt
      have hj8' : j.val < 8 := by scalar_tac
      have hcl : cur.val.length < Usize.max := by omega
      step*
      refine ⟨by omega, by omega, by simp [out1_post]; omega, ?_, by omega⟩
      rw [← heq, leBytesFrom_succ _ j.val.toNat 8 (by omega), out1_post]
      have hi4 : i4.val.toNat = j.val.toNat + 1 := by omega
      have hb : i3.bv = BitVec.ofNat 8 (x.val >>> (8 * j.val.toNat)) := by
        rw [i3_post, cast_u8_bv, i2_post, i1_post]; congr 2; omega
      simp [toBytes, hi4, hb]
    · simp only [WP.spec_ok]
      have : j.val.toNat = 8 := by scalar_tac
      rw [← heq, this, leBytesFrom_end]; simp
  · exact ⟨h0, h8, by simp, rfl⟩

theorem pushLenLoop_spec (out : alloc.vec.Vec U8) (x : U32) (i : I32)
    (h0 : 0 ≤ i.val) (h8 : i.val ≤ 4) (hcap : out.val.length + 4 ≤ Usize.max) :
    ext_data.push_len_prefixed_loop out x i ⦃ r =>
      toBytes r.val = toBytes out.val ++ leBytesFrom x.val i.val.toNat 4 ⦄ := by
  unfold ext_data.push_len_prefixed_loop
  apply loop.spec_decr_nat (fun (y : alloc.vec.Vec U8 × I32) => 4 - y.2.val.toNat)
    (fun y => 0 ≤ y.2.val ∧ y.2.val ≤ 4 ∧ y.1.val.length + (4 - y.2.val.toNat) ≤ out.val.length + 4 ∧
      toBytes y.1.val ++ leBytesFrom x.val y.2.val.toNat 4 = toBytes out.val ++ leBytesFrom x.val i.val.toNat 4)
  · rintro ⟨cur, j⟩ ⟨hj0, hj8, hc, heq⟩
    dsimp only at hj0 hj8 hc heq ⊢
    unfold ext_data.push_len_prefixed_loop.body
    split
    · rename_i hlt
      have hj8' : j.val < 4 := by scalar_tac
      have hcl : cur.val.length < Usize.max := by omega
      step*
      refine ⟨by omega, by omega, by simp [out1_post]; omega, ?_, by omega⟩
      rw [← heq, leBytesFrom_succ _ j.val.toNat 4 (by omega), out1_post]
      have hi4 : i4.val.toNat = j.val.toNat + 1 := by omega
      have hb : i3.bv = BitVec.ofNat 8 (x.val >>> (8 * j.val.toNat)) := by
        rw [i3_post, cast_u8_bv, i2_post, i1_post]; congr 2; omega
      simp [toBytes, hi4, hb]
    · simp only [WP.spec_ok]
      have : j.val.toNat = 4 := by scalar_tac
      rw [← heq, this, leBytesFrom_end]; simp
  · exact ⟨h0, h8, by simp, rfl⟩

private theorem natToBytesLE_eq (w n : ℕ) : LeanSpec.natToBytesLE w n = leBytesFrom n 0 w := by
  simp [LeanSpec.natToBytesLE, leBytesFrom]

theorem pushLenPrefixed_spec (out : alloc.vec.Vec U8) (bytes : Slice U8)
    (hcap : out.val.length + 4 + bytes.length ≤ Usize.max) :
    ext_data.push_len_prefixed out bytes ⦃ r =>
      (r.1 = true ↔ bytes.length < 2 ^ 32) ∧
      (r.1 = true → toBytes r.2.val = toBytes out.val ++ LeanSpec.vecU8 (toBytes bytes.val)) ⦄ := by
  unfold ext_data.push_len_prefixed
  simp only
  split
  · rename_i hgt
    simp only [WP.spec_ok, Bool.false_eq_true, false_iff, false_implies, and_true]
    scalar_tac
  · rename_i hle
    have hl : bytes.length < 2 ^ 32 := by scalar_tac
    step with UScalar.cast_inBounds_spec
    apply WP.spec_bind (pushLenLoop_spec out len 0#i32 (by simp) (by simp) (by omega))
    intro out1 h1
    have hlen : out1.val.length = out.val.length + 4 := by
      simpa [toBytes, leBytesFrom] using congrArg List.length h1
    have hcap1 : out1.val.length + (bytes.length - (0#usize).val) ≤ Usize.max := by
      simp only [Slice.length] at hcap ⊢; simp; omega
    apply WP.spec_bind (pushBytesLoop_spec out1 bytes 0#usize (by simp) hcap1)
    intro out2 h2
    simp only [WP.spec_ok, true_iff, forall_const]
    refine ⟨hl, ?_⟩
    rw [h2]
    simp only [toBytes, List.map_append] at h1 ⊢
    rw [h1, LeanSpec.vecU8, LeanSpec.u32LE, natToBytesLE_eq]
    simp [len_post]


private theorem natToBytesLE_succ (w n : ℕ) :
    LeanSpec.natToBytesLE (w + 1) n = BitVec.ofNat 8 n :: LeanSpec.natToBytesLE w (n >>> 8) := by
  simp only [LeanSpec.natToBytesLE, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp only [Function.comp, Nat.succ_eq_add_one]
  rw [show 8 * (a + 1) = 8 + 8 * a by ring, Nat.shiftRight_add]

/-- Re-encoding the little-endian value of a byte list gives back the bytes. -/
theorem natToBytesLE_leNat (l : List U8) :
    LeanSpec.natToBytesLE l.length (leNatOfList l) = toBytes l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b.val < 256 := by scalar_tac
    simp only [List.length_cons, natToBytesLE_succ, leNatOfList, List.foldr_cons, toBytes,
      List.map_cons] at ih ⊢
    have h1 : (b.val + 256 * List.foldr (fun b acc => b.val + 256 * acc) 0 l) >>> 8
        = List.foldr (fun b acc => b.val + 256 * acc) 0 l := by
      rw [Nat.shiftRight_eq_div_pow]; omega
    rw [h1, ih]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp

theorem leNatOfList_lt (l : List U8) : leNatOfList l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNatOfList]
  | cons b l ih =>
    have hb : b.val < 256 := by scalar_tac
    simp only [leNatOfList, List.foldr_cons, List.length_cons, pow_succ] at ih ⊢
    nlinarith

/-- The spec's serialization of a mapped address is the address's own 32 bytes. -/
theorem pubkeyToBytes_toPubkey (k : Pubkey) : LeanSpec.PubkeyToBytes (toPubkey k) = toBytes k.val := by
  have hlen : k.val.length = 32 := by simp
  have hlt : leNatOfList k.val < 2 ^ 256 := by
    have := leNatOfList_lt k.val; rw [hlen] at this; simpa using this
  simp only [LeanSpec.PubkeyToBytes, toPubkey, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have h := natToBytesLE_leNat k.val
  rw [hlen] at h; exact h

/-- The bytes `serialize_complete_ext_data` writes, as the spec writes them. -/
def extDataBytes (recipient feeRecipient mint : Pubkey) (ext : I64) (out1 out2 : Slice U8)
    (fee : U64) : LeanSpec.Bytes :=
  LeanSpec.PubkeyToBytes (toPubkey recipient) ++ LeanSpec.i64LE ext.val ++
    LeanSpec.vecU8 (toBytes out1.val) ++ LeanSpec.vecU8 (toBytes out2.val) ++
    LeanSpec.u64LE fee.val ++ LeanSpec.PubkeyToBytes (toPubkey feeRecipient) ++
    LeanSpec.PubkeyToBytes (toPubkey mint)

theorem serialize_spec (recipient feeRecipient mint : Pubkey) (ext : I64) (out1 out2 : Slice U8)
    (fee : U64) (hfit : out1.length + out2.length + 120 ≤ Usize.max) :
    ext_data.serialize_complete_ext_data recipient ext out1 out2 fee feeRecipient mint ⦃ r =>
      (r.isSome ↔ out1.length < 2 ^ 32 ∧ out2.length < 2 ^ 32) ∧
      ∀ v, r = some v → toBytes v.val = extDataBytes recipient feeRecipient mint ext out1 out2 fee ⦄ := by
  have tlen : ∀ l : List U8, (toBytes l).length = l.length := fun l => by simp [toBytes]
  have hk : ∀ k : Pubkey, k.val.length = 32 := fun k => by simp
  simp only [Slice.length] at hfit
  unfold ext_data.serialize_complete_ext_data
  simp only [lift, bind_tc_ok, ext_data.push_bytes, ext_data.push_u64_le]
  -- recipient
  apply WP.spec_bind (pushBytesLoop_spec (alloc.vec.Vec.new U8) (Array.to_slice recipient) 0#usize
    (by simp) (by simp [Slice.length]; omega))
  intro o1 h1
  have h1 : o1.val = recipient.val := by rw [h1]; simp
  -- ext_amount
  apply WP.spec_bind (pushU64Loop_spec o1 (IScalar.hcast .U64 ext) 0#i32 (by simp) (by simp)
    (by rw [h1, hk]; omega))
  intro o2 h2
  simp only [show (0#i32 : I32).val.toNat = 0 by simp] at h2
  have l2 : o2.val.length = 40 := by
    have := congrArg List.length h2; simp [tlen, leBytesFrom, h1, hk] at this; omega
  -- encrypted_output1
  apply WP.spec_bind (pushLenPrefixed_spec o2 out1 (by simp only [Slice.length]; omega))
  rintro ⟨b, o3⟩ ⟨hb, h3⟩
  simp only at hb h3 ⊢
  by_cases hbt : b = true
  · simp only [hbt]
    have l3 : o3.val.length = 44 + out1.val.length := by
      have := congrArg List.length (h3 hbt)
      simp [tlen, LeanSpec.vecU8, LeanSpec.u32LE, LeanSpec.natToBytesLE, l2] at this; omega
    apply WP.spec_bind (pushLenPrefixed_spec o3 out2 (by simp only [Slice.length]; omega))
    rintro ⟨b1, o4⟩ ⟨hb1, h4⟩
    simp only at hb1 h4 ⊢
    by_cases hb1t : b1 = true
    · simp only [hb1t]
      have l4 : o4.val.length = 48 + out1.val.length + out2.val.length := by
        have := congrArg List.length (h4 hb1t)
        simp [tlen, LeanSpec.vecU8, LeanSpec.u32LE, LeanSpec.natToBytesLE, l3] at this; omega
      apply WP.spec_bind (pushU64Loop_spec o4 fee 0#i32 (by simp) (by simp) (by omega))
      intro o5 h5
      simp only [show (0#i32 : I32).val.toNat = 0 by simp] at h5
      have l5 : o5.val.length = 56 + out1.val.length + out2.val.length := by
        have := congrArg List.length h5; simp [tlen, leBytesFrom, l4] at this; omega
      apply WP.spec_bind (pushBytesLoop_spec o5 (Array.to_slice feeRecipient) 0#usize
        (by simp) (by simp [Slice.length]; omega))
      intro o6 h6
      have h6 : o6.val = o5.val ++ feeRecipient.val := by rw [h6]; simp
      have l6 : o6.val.length = 88 + out1.val.length + out2.val.length := by
        rw [h6]; simp [hk]; omega
      apply WP.spec_bind (pushBytesLoop_spec o6 (Array.to_slice mint) 0#usize
        (by simp) (by simp [Slice.length]; omega))
      intro o7 h7
      have h7 : o7.val = o6.val ++ mint.val := by rw [h7]; simp
      simp only [WP.spec_ok, Option.isSome_some, true_iff, Option.some.injEq, forall_eq']
      refine ⟨⟨hb.mp hbt, hb1.mp hb1t⟩, ?_⟩
      rw [h7, h6]
      simp only [toBytes, List.map_append] at h5 h4 h3 h2 ⊢
      rw [h5, h4 hb1t, h3 hbt, h2, h1]
      simp only [extDataBytes, pubkeyToBytes_toPubkey, LeanSpec.i64LE, LeanSpec.u64LE,
        natToBytesLE_eq, toBytes, IScalar.hcast_val_eq, List.append_assoc]
      rfl
    · have hb1f' : b1 = false := by simpa using hb1t
      subst hb1f'
      apply (WP.spec_ok (none : Option (alloc.vec.Vec U8))).mpr
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and, reduceCtorEq,
        false_implies, forall_const, and_true]
      intro _ h; exact hb1t (hb1.mpr h)
  · have hbf' : b = false := by simpa using hbt
    subst hbf'
    apply (WP.spec_ok (none : Option (alloc.vec.Vec U8))).mpr
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff, not_and, reduceCtorEq,
      false_implies, forall_const, and_true]
    intro h; exact absurd (hb.mpr h) hbt

theorem toBytes_inj : ∀ {l1 l2 : List U8}, toBytes l1 = toBytes l2 → l1 = l2
  | [], [], _ => rfl
  | _ :: _, [], h => by simp [toBytes] at h
  | [], _ :: _, h => by simp [toBytes] at h
  | a :: l1, b :: l2, h => by
    simp only [toBytes, List.map_cons, List.cons.injEq] at h
    rw [U8.bv_eq_imp_eq a b h.1, toBytes_inj (l1 := l1) (l2 := l2) h.2]

private theorem toSlice_toBytes (v : alloc.vec.Vec U8) :
    toSlice (toBytes v.val) = alloc.vec.Vec.deref v := by
  have hl : (toBytes v.val).map (fun b => (⟨b⟩ : U8)) = v.val := by
    rw [toBytes, List.map_map]
    conv_rhs => rw [← List.map_id v.val]
    exact List.map_congr_left (fun x _ => rfl)
  simp only [toSlice, hl, alloc.vec.Vec.deref, dif_pos v.property]

theorem extDataHash_eq (sha : ext_data.Sha256 Unit) (recipient feeRecipient mint : Pubkey)
    (ext : I64) (out1 out2 : Slice U8) (fee : U64) (inputs : LeanSpec.TxInputs)
    (hA : inputs.A = toPubkey recipient) (hext : inputs.extAmt = ext.val)
    (he0 : inputs.encOut0 = toBytes out1.val) (he1 : inputs.encOut1 = toBytes out2.val)
    (hf : inputs.f = fee.val) (ht : inputs.t = toPubkey feeRecipient)
    (hm : inputs.mintAddr = toPubkey mint)
    (hfit : out1.length + out2.length + 120 ≤ Usize.max) :
    ext_data.calculate_complete_ext_data_hash sha recipient ext out1 out2 fee feeRecipient mint
      = if LeanSpec.encOutsFit inputs then
          (do let h ← sha.hash (toSlice (LeanSpec.serealizeExternalData inputs)); ok (some h))
        else ok none := by
  obtain ⟨r, hr, hsome, hbytes⟩ :=
    (WP.spec_equiv_exists _ _).mp (serialize_spec recipient feeRecipient mint ext out1 out2 fee hfit)
  have hser : LeanSpec.serealizeExternalData inputs = extDataBytes recipient feeRecipient mint ext out1 out2 fee := by
    simp only [LeanSpec.serealizeExternalData, extDataBytes, hA, hext, he0, he1, hf, ht, hm]
  have hfits : LeanSpec.encOutsFit inputs ↔ out1.length < 2 ^ 32 ∧ out2.length < 2 ^ 32 := by
    simp [LeanSpec.encOutsFit, he0, he1, toBytes, Slice.length]
  unfold ext_data.calculate_complete_ext_data_hash
  rw [hr]
  simp only [bind_tc_ok]
  cases r with
  | none =>
    have : ¬ LeanSpec.encOutsFit inputs := by rw [hfits, ← hsome]; simp
    simp [this]
  | some v =>
    have hfit' : LeanSpec.encOutsFit inputs := by rw [hfits, ← hsome]; simp
    rw [if_pos hfit', hser, ← hbytes v rfl, toSlice_toBytes]

end Connection
