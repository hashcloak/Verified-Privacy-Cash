import Connection.Proofs.WellFormed
import Connection.Proofs.Bridge
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: handler completeness

NOT FOR REVIEW: the statements are restated in `Connection/ConnectionTheorems.lean`.

If the spec's preconditions hold, the extracted `transact` handler returns `Ok` with the spec's
transfer and fee effects. The faithful statement fails (finding L1, and the all-zero `proof_a`,
see `ConnectionTheorems.lean`); the exact version excludes those two cases. -/

namespace Connection
open zkcash_core PrivacyCash.Proofs.G1 PrivacyCash.Proofs.Groth16

/-! ## The program's key: its G1 points decode (checked by computation) -/

unseal verifying_key.VERIFYING_KEY in
theorem key_alpha_decodes : (syscallDecodeG1 verifying_key.VERIFYING_KEY.vk_alpha_g1).isSome = true := by
  decide +kernel

unseal verifying_key.VERIFYING_KEY in
theorem key_ic_decodes : ∀ j, j < 8 →
    (syscallDecodeG1 (verifying_key.VERIFYING_KEY.vk_ic.val[j]!)).isSome = true := by
  decide +kernel

/-! ## `negate_g1` succeeds on every point except the all-zero bytes -/

/-- If arkworks decodes `a` (halves reversed), `negate_g1 a` returns a point. -/
theorem negateG1_some {a : Std.Array U8 64#usize} {P : G1Affine}
    (h : deserializeUncompressed (Std.Array.from (reverseHalves a.val) (reverseHalves_length a)) = some P) :
    ∃ a', negateG1 a = ok (some a') := by
  unfold negateG1
  obtain ⟨le, hce, hval⟩ := (WP.spec_equiv_exists _ _).mp (change_endianness_64 a)
  rw [hce, bind_tc_ok, toArray64_eq hval (by simp [reverseHalves])]
  rw [show ∀ x : Std.Array U8 64#usize, (some x >>= deserializeUncompressed) = deserializeUncompressed x
    from fun _ => rfl, h]
  obtain ⟨out, hce', hval'⟩ := (WP.spec_equiv_exists _ _).mp (change_endianness_64 P.neg.toBytes)
  simp only
  rw [hce', bind_tc_ok, toArray64_eq hval' (by simp [reverseHalves])]
  exact ⟨_, rfl⟩

/-- A point the syscalls decode, other than the all-zero bytes, is one arkworks decodes. -/
theorem deserialize_of_syscall {a : Std.Array U8 64#usize} {P : G1Affine}
    (h : syscallDecodeG1 a = some P) (hz : a.val ≠ List.replicate 64 0#u8) :
    deserializeUncompressed (Std.Array.from (reverseHalves a.val) (reverseHalves_length a)) = some P := by
  unfold syscallDecodeG1 at h
  rwa [if_neg hz] at h

/-- The all-zero bytes: the syscalls read the identity, `negate_g1` fails. -/
theorem negateG1_zeros {a : Std.Array U8 64#usize} (hz : a.val = List.replicate 64 0#u8) :
    negateG1 a = ok none := by
  unfold negateG1
  obtain ⟨le, hce, hval⟩ := (WP.spec_equiv_exists _ _).mp (change_endianness_64 a)
  rw [hce, bind_tc_ok, toArray64_eq hval (by simp [reverseHalves])]
  rw [show ∀ x : Std.Array U8 64#usize, (some x >>= deserializeUncompressed) = deserializeUncompressed x
    from fun _ => rfl, deserialize_zeros _ (by simp [hz, reverseHalves])]

/-! ## The verifier: `prepare_inputs` returns `vk_x` -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT] {s : AltBn128}

theorem prepare_inputs_complete (C : AltBn128Contracts s G1 G2 GT) (sys : SyscallsSucceed C)
    (pub : Std.Array (Std.Array U8 32#usize) 7#usize) (vk : groth16.VerifyingKey)
    (hk : ∀ j, j < 7 → k pub j < bn254ScalarModulus)
    (hic : ∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) ≠ none) :
    groth16.prepare_inputs (solanaBn254 s) pub vk ⦃ r => ∃ p, r = .Ok p ∧
      C.decodeG1 p = some (vkx C vk pub 7) ⦄ := by
  unfold groth16.prepare_inputs
  step*
  unfold groth16.prepare_inputs_loop
  apply loop.spec_decr_nat (fun (x : Std.Array U8 64#usize × Usize) => 7 - x.2.val)
    (fun x => x.2.val ≤ 7 ∧ (x.2.val = 0 → x.1 = vk.vk_ic.val[0]!) ∧
      (0 < x.2.val → C.decodeG1 x.1 = some (vkx C vk pub x.2.val)))
  · rintro ⟨prep, i⟩ ⟨hi, h0, hpos⟩
    dsimp only at hi h0 hpos ⊢
    unfold groth16.prepare_inputs_loop.body
    split
    · simp only [solanaBn254]
      rename_i hlt
      have hi7 : i.val < 7 := by simp [groth16.NR_PUBLIC_INPUTS] at hlt; scalar_tac
      -- the running sum decodes
      have hprep : C.decodeG1 prep ≠ none := by
        rcases Nat.eq_zero_or_pos i.val with h0' | hpos'
        · rw [h0 h0']; exact hic 0 (by omega)
        · rw [hpos hpos']; simp
      step*
      · -- multiplication answered `none`: impossible (its point decodes)
        rename_i hmul
        have ha1 : a1 = vk.vk_ic.val[i.val + 1]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
          simp [a1_post, i1_post]
        obtain ⟨out, hout⟩ := sys.mul (concatArrays a1 input (by simp))
          (by rw [bytesAt_concat_left, ha1]; exact hic _ (by omega))
        rw [hout] at hmul; cases hmul
      · -- addition answered `none`: impossible (both points decode)
        rename_i hmul hadd
        obtain ⟨P, hP, hp⟩ := C.mul _ _ hmul
        obtain ⟨out, hout⟩ := sys.add (concatArrays p prep (by simp))
          (by rw [bytesAt_concat_left, hp]; simp)
          (by rw [bytesAt_concat_right _ _ _ 64 (by simp)]; exact hprep)
        rw [hout] at hadd; cases hadd
      · -- one step: k_i · IC_{i+1} is added to the running sum
        rename_i hmul hadd
        obtain ⟨P, hP, hp⟩ := C.mul _ _ hmul
        obtain ⟨P', Q, hP', hQ, hp1⟩ := C.add _ _ hadd
        rw [bytesAt_concat_left] at hP hP'
        rw [bytesAt_concat_right _ _ _ 64 (by simp)] at hp hQ
        rw [hp] at hP'
        cases hP'
        have hi1 : i1.val = i.val + 1 := i1_post
        have ha1 : a1 = vk.vk_ic.val[i.val + 1]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
          simp [a1_post, hi1]
        have hin : input = pub.val[i.val]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
          simp [input_post]
        rw [ha1] at hP
        have hPic : ic C vk (i.val + 1) = P := by unfold ic; rw [hP]; rfl
        have hkin : beNatOf input = k pub i.val := by simp [k, hin]
        refine ⟨by omega, fun h => by omega, fun _ => ?_, by omega⟩
        rcases Nat.eq_zero_or_pos i.val with h0' | hpos'
        · have hprep' : prep = vk.vk_ic.val[0]! := h0 h0'
          rw [hprep'] at hQ
          have hQic : ic C vk 0 = Q := by unfold ic; rw [hQ]; rfl
          rw [hp1, hi1, h0', hkin]
          rw [h0'] at hPic
          simp [vkx, hPic, hQic, add_comm, h0']
        · have hacc := hpos hpos'
          have hQ' : Q = vkx C vk pub i.val := by rw [hQ] at hacc; exact Option.some.inj hacc
          rw [hp1, hi1, hQ', ← hPic, hkin]
          simp only [vkx, Finset.sum_range_succ]
          abel_nf
      · -- the range check failed: impossible (the input is canonical)
        rename_i hbf
        have hin : input = pub.val[i.val]! := by
          rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega)]
          simp [input_post]
        apply absurd _ hbf
        rw [b_post, decide_eq_true_eq]
        have := hk i.val hi7
        simpa [k, ← hin] using this
    · rename_i hge
      have hi7 : i.val = 7 := by simp [groth16.NR_PUBLIC_INPUTS] at hge; scalar_tac
      simp only [WP.spec_ok]
      obtain hacc := hpos (by omega)
      rw [hi7] at hacc
      exact ⟨prep, rfl, hacc⟩
  · refine ⟨by simp, fun _ => ?_, fun h => by simp at h⟩
    rw [prepared_public_inputs_post, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
    rfl
end

/-- **A0**: with `proof_a` the 64 zero bytes, the program's verifier rejects, whatever the rest. -/
theorem verifyProof_zeroA {s : AltBn128} (proof : transact.Proof) (vk : groth16.VerifyingKey)
    (hz : proof.proof_a.val = List.replicate 64 0#u8) :
    groth16.verify_proof (solanaBn254 s) proof vk = ok false := by
  unfold groth16.verify_proof
  obtain ⟨_, h0', rfl⟩ := (WP.spec_equiv_exists _ _).mp
    (Std.Array.index_usize_spec proof.input_nullifiers 0#usize (by simp))
  obtain ⟨_, h1', rfl⟩ := (WP.spec_equiv_exists _ _).mp
    (Std.Array.index_usize_spec proof.input_nullifiers 1#usize (by simp))
  obtain ⟨_, h2', rfl⟩ := (WP.spec_equiv_exists _ _).mp
    (Std.Array.index_usize_spec proof.output_commitments 0#usize (by simp))
  obtain ⟨_, h3', rfl⟩ := (WP.spec_equiv_exists _ _).mp
    (Std.Array.index_usize_spec proof.output_commitments 1#usize (by simp))
  rw [h0', bind_tc_ok, h1', bind_tc_ok, h2', bind_tc_ok, h3', bind_tc_ok,
    show (solanaBn254 s).negate_g1 proof.proof_a = ok none from negateG1_zeros hz, bind_tc_ok]

/-! ## The verifier: `verify` and `verify_proof` accept -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT] {s : AltBn128}
set_option linter.unusedSimpArgs false

theorem verify_complete (C : AltBn128Contracts s G1 G2 GT) (sys : SyscallsSucceed C)
    (pa : Std.Array U8 64#usize) (pb : Std.Array U8 128#usize)
    (pc : Std.Array U8 64#usize) (pub : Std.Array (Std.Array U8 32#usize) 7#usize)
    (vk : groth16.VerifyingKey)
    (hk : ∀ j, j < 7 → k pub j < bn254ScalarModulus)
    (hic : ∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) ≠ none)
    (A Cp α : G1) (B β γ δ : G2)
    (d1 : C.decodeG1 pa = some A) (d2 : C.decodeG2 pb = some B) (d3 : C.decodeG1 pc = some Cp)
    (d4 : C.decodeG1 vk.vk_alpha_g1 = some α) (d5 : C.decodeG2 vk.vk_beta_g2 = some β)
    (d6 : C.decodeG2 vk.vk_gamme_g2 = some γ) (d7 : C.decodeG2 vk.vk_delta_g2 = some δ)
    (heq : C.e A B * C.e (vkx C vk pub 7) γ * C.e Cp δ * C.e α β = 1) :
    groth16.verify (solanaBn254 s) pa pb pc pub vk ⦃ r => r = .Ok true ⦄ := by
  unfold groth16.verify
  apply WP.spec_bind (prepare_inputs_complete C sys pub vk hk hic)
  rintro r ⟨p, rfl, hp⟩
  simp only [solanaBn254]
  step*
  all_goals (
    have sA : bytesAt pairing_input8 0 64#usize (by simp) = pa :=
      bytesAt_eq_of _ _ _ _ fun t ht => by
        have ht' : t < 64 := by simpa using ht
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, if_neg, Nat.add_sub_cancel_left]
    have sB : bytesAt pairing_input8 64 128#usize (by simp) = pb :=
      bytesAt_eq_of _ _ _ _ fun t ht => by
        have ht' : t < 128 := by simpa using ht
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, if_neg, Nat.add_sub_cancel_left]
    have sP : bytesAt pairing_input8 192 64#usize (by simp) = p :=
      bytesAt_eq_of _ _ _ _ fun t ht => by
        have ht' : t < 64 := by simpa using ht
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, if_neg, Nat.add_sub_cancel_left]
    have sG : bytesAt pairing_input8 256 128#usize (by simp) = vk.vk_gamme_g2 :=
      bytesAt_eq_of _ _ _ _ fun t ht => by
        have ht' : t < 128 := by simpa using ht
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, if_neg, Nat.add_sub_cancel_left]
    have sC : bytesAt pairing_input8 384 64#usize (by simp) = pc :=
      bytesAt_eq_of _ _ _ _ fun t ht => by
        have ht' : t < 64 := by simpa using ht
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, if_neg, Nat.add_sub_cancel_left]
    have sD : bytesAt pairing_input8 448 128#usize (by simp) = vk.vk_delta_g2 :=
      bytesAt_eq_of _ _ _ _ fun t ht => by
        have ht' : t < 128 := by simpa using ht
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, if_neg, Nat.add_sub_cancel_left]
    have sAl : bytesAt pairing_input8 576 64#usize (by simp) = vk.vk_alpha_g1 :=
      bytesAt_eq_of _ _ _ _ fun t ht => by
        have ht' : t < 64 := by simpa using ht
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, if_neg, Nat.add_sub_cancel_left]
    have sBe : bytesAt pairing_input8 640 128#usize (by simp) = vk.vk_beta_g2 :=
      bytesAt_eq_of _ _ _ _ fun t ht => by
        have ht' : t < 128 := by simpa using ht
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, if_neg, Nat.add_sub_cancel_left]
    obtain ⟨out, hout, hiff⟩ := sys.pairing pairing_input8 A (vkx C vk pub 7) Cp α B γ δ β
      (by rw [sA]; exact d1) (by rw [sB]; exact d2) (by rw [sP]; exact hp) (by rw [sG]; exact d6)
      (by rw [sC]; exact d3) (by rw [sD]; exact d7) (by rw [sAl]; exact d4) (by rw [sBe]; exact d5))
  · rename_i hn; rw [hn] at hout; cases hout
  · rename_i hsome hne
    rw [hsome] at hout; cases hout
    have h31 := hiff.mpr heq
    have hi : i = 1#u8 := by
      rw [i_post, ← h31, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]; rfl
    rw [hi] at hne; exact absurd hne (by decide)

end

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [CommGroup GT] {s : AltBn128}

theorem verifyProof_complete (C : AltBn128Contracts s G1 G2 GT) (sys : SyscallsSucceed C) (laws : ∀ (a : G1) (b : G2), C.e (-a) b = (C.e a b)⁻¹)
    (proof : transact.Proof) (vk : groth16.VerifyingKey)
    (hcan : ∀ j, j < 7 → beNatOf ((publicInputs proof)[j]!) < bn254ScalarModulus)
    (hic : ∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) ≠ none)
    (hz : proof.proof_a.val ≠ List.replicate 64 0#u8)
    (A Cp α : G1) (B β γ δ : G2)
    (d1 : C.decodeG1 proof.proof_a = some A) (d2 : C.decodeG2 proof.proof_b = some B)
    (d3 : C.decodeG1 proof.proof_c = some Cp)
    (d4 : C.decodeG1 vk.vk_alpha_g1 = some α) (d5 : C.decodeG2 vk.vk_beta_g2 = some β)
    (d6 : C.decodeG2 vk.vk_gamme_g2 = some γ) (d7 : C.decodeG2 vk.vk_delta_g2 = some δ)
    (heq : C.e A B = C.e α β * C.e (vkxOf C vk proof) γ * C.e Cp δ) :
    groth16.verify_proof (solanaBn254 s) proof vk = ok true := by
  -- negation succeeds and gives -A
  rw [C.decodeG1_eq] at d1
  obtain ⟨P, hP, hPA⟩ := Option.map_eq_some_iff.mp d1
  obtain ⟨a', hneg⟩ := negateG1_some (deserialize_of_syscall hP hz)
  obtain ⟨P', hP', hP'a⟩ := negateG1_decode hneg
  rw [hP] at hP'; obtain rfl := Option.some.inj hP'
  have dA' : C.decodeG1 a' = some (-A) := by
    rw [C.decodeG1_eq, hP'a, Option.map_some, C.embed_neg, hPA]
  set pub : Std.Array (Std.Array U8 32#usize) 7#usize := Std.Array.make 7#usize [proof.root,
    proof.public_amount, proof.ext_data_hash, proof.input_nullifiers.val[0], proof.input_nullifiers.val[1],
    proof.output_commitments.val[0], proof.output_commitments.val[1]] (by simp) with hpubdef
  have hpub : ∀ j, k pub j = beNatOf ((publicInputs proof)[j]!) := by
    intro j; simp [hpubdef, k, publicInputs, Std.Array.make, List.getElem!_eq_getElem?_getD]
  have hvkx : vkxOf C vk proof = vkx C vk pub 7 := by simp only [vkxOf, vkx, hpub]
  have heq' : C.e (-A) B * C.e (vkx C vk pub 7) γ * C.e Cp δ * C.e α β = 1 := by
    rw [laws, ← hvkx]
    have e1 : (C.e A B)⁻¹ * C.e (vkxOf C vk proof) γ * C.e Cp δ * C.e α β
        = (C.e A B)⁻¹ * (C.e α β * C.e (vkxOf C vk proof) γ * C.e Cp δ) := by ac_rfl
    rw [e1, inv_mul_eq_one, heq]
  obtain ⟨r, hr, hrt⟩ := (WP.spec_equiv_exists _ _).mp (verify_complete C sys a' proof.proof_b proof.proof_c pub vk
    (fun j hj => by rw [hpub]; exact hcan j hj) hic (-A) Cp α B β γ δ dA' d2 d3 d4 d5 d6 d7 heq')
  subst hrt
  unfold groth16.verify_proof
  obtain ⟨_, h0', rfl⟩ := (WP.spec_equiv_exists _ _).mp
    (Std.Array.index_usize_spec proof.input_nullifiers 0#usize (by simp))
  obtain ⟨_, h1', rfl⟩ := (WP.spec_equiv_exists _ _).mp
    (Std.Array.index_usize_spec proof.input_nullifiers 1#usize (by simp))
  obtain ⟨_, h2', rfl⟩ := (WP.spec_equiv_exists _ _).mp
    (Std.Array.index_usize_spec proof.output_commitments 0#usize (by simp))
  obtain ⟨_, h3', rfl⟩ := (WP.spec_equiv_exists _ _).mp
    (Std.Array.index_usize_spec proof.output_commitments 1#usize (by simp))
  rw [h0', bind_tc_ok, h1', bind_tc_ok, h2', bind_tc_ok, h3', bind_tc_ok,
    show (solanaBn254 s).negate_g1 proof.proof_a = ok (some a') from hneg, bind_tc_ok]
  show (do let r ← groth16.verify (solanaBn254 s) a' proof.proof_b proof.proof_c pub vk
           match r with
           | core.result.Result.Ok v => ok v
           | core.result.Result.Err _ => ok false) = ok true
  rw [hr, bind_tc_ok]
end

/-! ## The verifier bridge, converse -/

section
set_option linter.unusedSectionVars false
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] {s : AltBn128}

theorem syscallGroups_decodeG1 (C : AltBn128Contracts s G1 G2 GT) (b : Std.Array U8 64#usize) :
    (syscallGroups C).decodeG1 (toBytes b.val) = C.decodeG1 b := by
  show (toArray 64#usize (toBytes b.val)).bind C.decodeG1 = _
  rw [toArray_toBytes]; rfl

theorem syscallGroups_decodeG2 (C : AltBn128Contracts s G1 G2 GT) (b : Std.Array U8 128#usize) :
    (syscallGroups C).decodeG2 (toBytes b.val) = C.decodeG2 b := by
  show (toArray 128#usize (toBytes b.val)).bind C.decodeG2 = _
  rw [toArray_toBytes]; rfl

/-- What a decoded mapped proof is: the points the syscalls read from its bytes. -/
theorem decode_toInputs_inv (C : AltBn128Contracts s G1 G2 GT) (proof : zkcash_core.transact.Proof)
    (a : TransactAccounts) (ext : I64) (fee : U64) (out1 out2 : Slice U8)
    : letI : LeanSpec.Groups := syscallGroups C
    ∀ π : LeanSpec.Groth16.Proof, (toInputs a proof ext fee out1 out2).π.decode = some π →
      C.decodeG1 proof.proof_a = some π.A ∧ C.decodeG2 proof.proof_b = some π.B ∧
      C.decodeG1 proof.proof_c = some π.C := by
  intro π h
  unfold LeanSpec.Groth16.ProofBytes.decode at h
  simp only [toInputs] at h
  rw [syscallGroups_decodeG1, syscallGroups_decodeG2, syscallGroups_decodeG1] at h
  cases hA : C.decodeG1 proof.proof_a <;> cases hB : C.decodeG2 proof.proof_b <;>
    cases hC : C.decodeG1 proof.proof_c <;> rw [hA, hB, hC] at h <;> simp at h
  subst h; exact ⟨rfl, rfl, rfl⟩


/-- The program key's points decode (G1: by computation; G2: `KeyG2Decodes`). -/
theorem key_decodes (C : AltBn128Contracts s G1 G2 GT) (key : KeyG2Decodes C) :
    let vk := zkcash_core.verifying_key.VERIFYING_KEY
    (∃ α, C.decodeG1 vk.vk_alpha_g1 = some α) ∧ (∃ β, C.decodeG2 vk.vk_beta_g2 = some β) ∧
    (∃ γ, C.decodeG2 vk.vk_gamme_g2 = some γ) ∧ (∃ δ, C.decodeG2 vk.vk_delta_g2 = some δ) ∧
    (∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) ≠ none) := by
  intro vk
  refine ⟨?_, Option.ne_none_iff_exists'.mp key.beta, Option.ne_none_iff_exists'.mp key.gamma,
    Option.ne_none_iff_exists'.mp key.delta, fun j hj => ?_⟩
  · have h : (syscallDecodeG1 vk.vk_alpha_g1).isSome = true := key_alpha_decodes
    rw [C.decodeG1_eq]
    cases hd : syscallDecodeG1 vk.vk_alpha_g1 with
    | none => rw [hd] at h; simp at h
    | some P => exact ⟨_, rfl⟩
  · have h : (syscallDecodeG1 (vk.vk_ic.val[j]!)).isSome = true := key_ic_decodes j hj
    rw [C.decodeG1_eq]
    cases hd : syscallDecodeG1 (vk.vk_ic.val[j]!) with
    | none => rw [hd] at h; simp at h
    | some P => simp

/-- **The verifier bridge, converse.** If the spec's `proofValid` holds for the mapped
    transaction, its public inputs are canonical and `proof_a` is not the all-zero bytes, the
    program's verifier accepts. -/
theorem programVerifier_complete (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) (sys : SyscallsSucceed C) (key : KeyG2Decodes C)
    (proof : zkcash_core.transact.Proof) (a : TransactAccounts) (ext : I64) (fee : U64)
    (out1 out2 : Slice U8)
    (hcan : ∀ j, j < 7 → Canonical ((publicInputs proof)[j]!))
    (hz : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    LeanSpec.proofValid (toInputs a proof ext fee out1 out2) → c.proofVerifier.verify proof = ok true := by
  intro hpv
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  obtain ⟨π, hdec, hver⟩ := hpv
  obtain ⟨dA, dB, dC⟩ := decode_toInputs_inv C proof a ext fee out1 out2 π hdec
  obtain ⟨⟨α, hα⟩, ⟨β, hβ⟩, ⟨γ, hγ⟩, ⟨δ, hδ⟩, hic⟩ := key_decodes C key
  have hvec : ∀ i : Fin 7, LeanSpec.Groth16.toVector (toInputs a proof ext fee out1 out2).pubInputs i
      = toF ((publicInputs proof)[i.val]!) := by
    intro i; fin_cases i <;> rfl
  have hsmul : ∀ (b : Std.Array U8 32#usize) (P : G1), toF b • P = beNatOf b • P := by
    intro b P
    show ((beNat b : ℕ) : LeanSpec.F) • P = _
    rw [Nat.cast_smul_eq_nsmul]; rfl
  have hvkx : ic C zkcash_core.verifying_key.VERIFYING_KEY 0 +
      ∑ i : Fin 7, LeanSpec.Groth16.toVector (toInputs a proof ext fee out1 out2).pubInputs i •
        ic C zkcash_core.verifying_key.VERIFYING_KEY i.succ.val
      = vkxOf C zkcash_core.verifying_key.VERIFYING_KEY proof := by
    simp only [vkxOf, hvec, hsmul, Fin.val_succ]
    rw [Fin.sum_univ_eq_sum_range (fun j => beNatOf ((publicInputs proof)[j]!) •
      ic C zkcash_core.verifying_key.VERIFYING_KEY (j + 1)) 7]
  have hver' : C.e π.A π.B
      = C.e ((C.decodeG1 zkcash_core.verifying_key.VERIFYING_KEY.vk_alpha_g1).getD 0)
          ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_beta_g2).getD 0) *
        C.e (ic C zkcash_core.verifying_key.VERIFYING_KEY 0 +
          ∑ i : Fin 7, LeanSpec.Groth16.toVector (toInputs a proof ext fee out1 out2).pubInputs i •
            ic C zkcash_core.verifying_key.VERIFYING_KEY i.succ.val)
          ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_gamme_g2).getD 0) *
        C.e π.C ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_delta_g2).getD 0) := hver
  rw [hα, hβ, hγ, hδ, hvkx] at hver'
  simp only [Option.getD_some] at hver'
  exact verifyProof_complete C sys laws.neg_left proof _ (fun j hj => hcan j hj) hic hz
    π.A π.C α π.B β γ δ dA dB dC hα hβ hγ hδ hver'

end

/-! ## The Merkle tree: `append`'s loop runs to the end -/

/-- `append`'s loop returns, with canonical subtrees and a canonical hash, when its inputs are
    canonical and Poseidon answers on canonical inputs. -/
theorem appendLoop_complete (H : merkle_tree.Hasher Unit)
    (hpc : ∀ a b h, H.hash_pair a b = ok h → Canonical h)
    (hs : ∀ a b, Canonical a → Canonical b → ∃ h, H.hash_pair a b = ok h)
    (z : Std.Array (Std.Array U8 32#usize) 41#usize) (hzb : H.zero_bytes = ok z)
    (hzc : ∀ i, i ≤ 26 → Canonical (z.val[i]!))
    (iter : core.ops.range.Range Usize) (a : Std.Array (Std.Array U8 32#usize) 26#usize)
    (ci : Usize) (cur : Std.Array U8 32#usize) (proof : alloc.vec.Vec (Std.Array U8 32#usize))
    (hk : iter.start.val ≤ 26) (hend : iter.end.val = 26) (hplen : proof.length = 26)
    (ha : ∀ i, i < 26 → Canonical (a.val[i]!)) (hcur : Canonical cur) :
    merkle_tree.append_loop H iter a ci cur proof ⦃ r =>
      (∀ i, i < 26 → Canonical (r.1.val[i]!)) ∧ Canonical r.2.1 ⦄ := by
  unfold merkle_tree.append_loop
  apply loop.spec_decr_nat
    (fun x : (core.ops.range.Range Usize) × (Std.Array (Std.Array U8 32#usize) 26#usize)
        × Usize × (Std.Array U8 32#usize) × (alloc.vec.Vec (Std.Array U8 32#usize)) => 26 - x.1.start.val)
    (fun x => x.1.start.val ≤ 26 ∧ x.1.end.val = 26 ∧ x.2.2.2.2.length = 26 ∧
      (∀ i, i < 26 → Canonical (x.2.1.val[i]!)) ∧ Canonical x.2.2.2.1)
  · rintro ⟨it, a, ci, cur, proof⟩ ⟨hk, hend, hplen, ha, hcur⟩
    dsimp only at hk hend hplen ha hcur ⊢
    unfold merkle_tree.append_loop.body
    step*
    rename_i hoi
    have hlt : it.start.val < it.end.val := by
      by_contra hc; rw [if_neg hc] at o_post; rw [o_post.1] at hoi; cases hoi
    rw [if_pos hlt] at o_post
    obtain ⟨ho, hs1⟩ := o_post
    rw [ho] at hoi; cases hoi
    have hi : it.start.val < 26 := by omega
    rw [hzb, bind_tc_ok]
    step*
    have hzbc : Canonical zero_byte := by
      have := hzc it.start.val (by omega)
      rw [getElem!_pos _ _ (by simp; omega)] at this
      rw [zero_byte_post]; exact this
    have hsubc : Canonical subtree := by
      have := ha it.start.val hi
      rw [getElem!_pos _ _ (by simp; omega)] at this
      rw [subtree_post]; exact this
    split
    · step*
      obtain ⟨x1, x2⟩ := x
      simp only at x_post1
      subst x_post1
      obtain ⟨hh, hhash⟩ := hs cur zero_byte (by assumption) (by assumption)
      refine WP.spec_bind (Pₘ := fun y => y = (cur, zero_byte, proof.set it.start zero_byte))
        ((WP.spec_ok _).mpr rfl) ?_
      rintro y rfl
      refine WP.spec_bind (m := H.hash_pair cur zero_byte) (Pₘ := fun y => y = hh)
        (by rw [hhash]; exact (WP.spec_ok _).mpr rfl) ?_
      rintro y rfl
      step*
      refine ⟨by omega, by rw [o_post1]; exact hend, by simp [hplen], ?_, hpc _ _ _ hhash, by omega⟩
      intro j hj
      rw [index_mut_back_post]
      simp only [Std.Array.set_val_eq]
      by_cases hji : j = it.start.val
      · rw [getElem!_pos _ _ (by simp; omega)]; simp [hji]; assumption
      · rw [getElem!_pos _ _ (by simp; omega)]
        have := ha j hj
        rw [getElem!_pos _ _ (by simp; omega)] at this
        have hne : it.start.val ≠ j := Ne.symm hji
        simpa [hne] using this
    · step*
      obtain ⟨x1, x2⟩ := x
      simp only at x_post1
      subst x_post1
      obtain ⟨hh, hhash⟩ := hs subtree cur (by assumption) (by assumption)
      refine WP.spec_bind (Pₘ := fun y => y = (subtree, cur, proof.set it.start subtree))
        ((WP.spec_ok _).mpr rfl) ?_
      rintro y rfl
      refine WP.spec_bind (m := H.hash_pair subtree cur) (Pₘ := fun y => y = hh)
        (by rw [hhash]; exact (WP.spec_ok _).mpr rfl) ?_
      rintro y rfl
      step*
      refine ⟨by omega, by rw [o_post1]; exact hend, by simp [hplen], ?_, hpc _ _ _ hhash, by omega⟩
      intro j hj
      rw [index_mut_back_post]
      simp only [Std.Array.set_val_eq]
      by_cases hji : j = it.start.val
      · rw [getElem!_pos _ _ (by simp; omega)]; simp [hji]; assumption
      · rw [getElem!_pos _ _ (by simp; omega)]
        have := ha j hj
        rw [getElem!_pos _ _ (by simp; omega)] at this
        have hne : it.start.val ≠ j := Ne.symm hji
        simpa [hne] using this
  · exact ⟨hk, hend, hplen, ha, hcur⟩

/-- `x.ok_or e` followed by `?`, on a `some`: continues with the value. -/
theorem okOr_some_spec {T β : Type} (v : T) (e : error.ErrorCode)
    (k : core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible error.ErrorCode) T → Result β)
    (P : β → Prop) (h : (k (.Continue v)) ⦃ P ⦄) :
    (do let r ← core.option.Option.ok_or (some v) e
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        k cf) ⦃ P ⦄ := by
  have e1 : core.option.Option.ok_or (some v) e = ok (core.result.Result.Ok v) := by
    simp [core.option.Option.ok_or]
  have e2 : core.result.Result.Insts.CoreOpsTry.branch (core.result.Result.Ok v : core.result.Result T error.ErrorCode)
      = ok (.Continue v) := by simp [core.result.Result.Insts.CoreOpsTry.branch]
  rw [e1, bind_tc_ok, e2, bind_tc_ok]; exact h

/-- `append` returns `Ok` when there is room, its inputs are canonical and Poseidon answers on
    canonical inputs; the new subtrees are canonical. -/
theorem append_complete (H : merkle_tree.Hasher Unit)
    (hpc : ∀ a b h, H.hash_pair a b = ok h → Canonical h)
    (hs : ∀ a b, Canonical a → Canonical b → ∃ h, H.hash_pair a b = ok h)
    (z : Std.Array (Std.Array U8 32#usize) 41#usize) (hzb : H.zero_bytes = ok z)
    (hzc : ∀ i, i ≤ 26 → Canonical (z.val[i]!))
    (leaf : Std.Array U8 32#usize) (t : merkle_tree.MerkleTreeAccount)
    (hshape : TreeShape t) (hroom : t.next_index.val < 2 ^ 26)
    (hsub : ∀ i, i < 26 → Canonical (t.subtrees.val[i]!)) (hleaf : Canonical leaf) :
    merkle_tree.append H leaf t ⦃ r => ∃ p, r.1 = .Ok p ∧
      ∀ i, i < 26 → Canonical (r.2.subtrees.val[i]!) ⦄ := by
  obtain ⟨hheight, hsize, hidx⟩ := hshape
  unfold merkle_tree.append
  step*
  · obtain ⟨a', ha', heq⟩ := (WP.spec_equiv_exists _ _).mp (core.array.CloneArray.clone_spec
      core.clone.CloneU8 (Std.Array.repeat 32#usize 0#u8) (by intro x _; rfl))
    show core.array.CloneArray.clone core.clone.CloneU8 _ = _
    rw [ha', ← heq]
  · have hh : height.val = 26 := by rw [height_post]; simp [hheight]
    step with appendLoop_complete H hpc hs z hzb hzc { start := 0#usize, «end» := height } _ _ _ _ (by simp) (by simpa using hh)
      (by rw [proof_post1, hh]) hsub hleaf
    step*
    cases o with
    | none => simp at o_post; scalar_tac
    | some z1 =>
    apply okOr_some_spec
    step*
    cases o1 with
    | none =>
      have hi : i.val = t.root_index.val := by
        rw [i_post]; exact UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by scalar_tac)
      simp at o1_post; scalar_tac
    | some z2 =>
    apply okOr_some_spec
    step*
  · rename_i hfull
    exfalso; apply hfull
    have : max_capacity.val = 2 ^ 26 := by
      rw [max_capacity_post, height_post]; simp [hheight, U64.size, U64.numBits]
    show t.next_index.val < max_capacity.val
    omega

/-! ## The handler, at the code level: it returns `Ok` when each of its steps succeeds -/

/-- One bind whose step is known: `m = ok v`. -/
theorem spec_bind_eq {α β : Type} {m : Result α} {v : α} {k : α → Result β} {P : β → Prop}
    (h : m = ok v) (hk : (k v) ⦃ P ⦄) : (m >>= k) ⦃ P ⦄ := by
  rw [h, bind_tc_ok]; exact hk

theorem spec_ite_pos' {α : Type} {c : Prop} [Decidable c] {x y : Result α} {P : α → Prop}
    (hc : c) (h : x ⦃ P ⦄) : (if c then x else y) ⦃ P ⦄ := by rw [if_pos hc]; exact h

theorem spec_ite_neg' {α : Type} {c : Prop} [Decidable c] {x y : Result α} {P : α → Prop}
    (hc : ¬ c) (h : y ⦃ P ⦄) : (if c then x else y) ⦃ P ⦄ := by rw [if_neg hc]; exact h

syntax "bpos " term : tactic
macro_rules
  | `(tactic| bpos $h) => `(tactic| refine spec_ite_pos' $h ?_)
syntax "bneg " term : tactic
macro_rules
  | `(tactic| bneg $h) => `(tactic| refine spec_ite_neg' $h ?_)

syntax "bstep " term : tactic
macro_rules
  | `(tactic| bstep $h) => `(tactic| refine spec_bind_eq $h ?_)

theorem checked_add_ok (x y : U64) (h : x.val + y.val ≤ U64.max) :
    ∃ z, x.checked_add y = some z ∧ z.val = x.val + y.val := by
  have hs := U64.checked_add_bv_spec x y
  cases hc : x.checked_add y with
  | none => rw [hc] at hs; omega
  | some z => rw [hc] at hs; exact ⟨z, rfl, hs.2.1⟩

theorem checked_sub_ok (x y : U64) (h : y.val ≤ x.val) :
    ∃ z, x.checked_sub y = some z ∧ z.val = x.val - y.val := by
  have hs := U64.checked_sub_bv_spec x y
  cases hc : x.checked_sub y with
  | none => rw [hc] at hs; omega
  | some z => rw [hc] at hs; exact ⟨z, rfl, hs.2.1⟩

theorem idx2_ok (x : Std.Array (Std.Array U8 32#usize) 2#usize) (k : Usize) (hk : k.val < 2) :
    x.index_usize k = ok (x.val[k.val]!) := by
  obtain ⟨v', hv', hvv⟩ := (WP.spec_equiv_exists _ _).mp (Std.Array.index_usize_spec x k (by simp; omega))
  rw [hv', hvv, getElem!_pos _ _ (by simp; omega)]

/-- The system transfer succeeds when the source is a system account with enough lamports and
    the destination does not overflow. -/
theorem systemTransfer_ok (e : SolEnv) (src dst : Pubkey) (amt : U64)
    (ho : (e.accounts src).owner = systemProgram) (hd : (e.accounts src).data.isEmpty)
    (hle : amt.val ≤ (e.balances src).val) (hne : src ≠ dst)
    (hfit : (e.balances dst).val + amt.val ≤ U64.max) :
    ∃ e', e.systemTransfer src dst amt = some e' := by
  unfold SolEnv.systemTransfer systemTransferBalances
  rw [if_pos ⟨ho, hd, hle⟩]
  simp only
  rw [if_pos (by simp only [setBalance, if_neg (Ne.symm hne)]; exact hfit)]
  exact ⟨_, rfl⟩

theorem handler_complete_code (c : Crypto) (env : SolEnv) (tree : merkle_tree.MerkleTreeAccount)
    (config : admin.GlobalConfig) (proof : transact.Proof) (ext : I64) (fee : U64)
    (recipient feeRecipient : Pubkey) (out1 out2 : Slice U8) (hsh : Std.Array U8 32#usize) (v : U64)
    (hroot : merkle_tree.is_known_root tree proof.root = ok true)
    (hext : ext_data.calculate_complete_ext_data_hash c.sha256 recipient ext out1 out2 fee
      feeRecipient transact.SOL_ADDRESS = ok (some hsh))
    (hexteq : (leNat hsh : Fr) = (beNat proof.ext_data_hash : Fr))
    (hpub : utils.check_public_amount arkFr ext fee proof.public_amount = ok true)
    (hfee : utils.validate_fee ext fee config.deposit_fee_rate config.withdrawal_fee_rate
      config.fee_error_margin = ok (.Ok ()))
    (hver : c.proofVerifier.verify proof = ok true)
    (hrent : env.rentExemptMinimum = some v)
    (hext0 : ext.val ≠ 0) (hmin : ext.val ≠ -9223372036854775808)
    (hD : ext.val > 0 →
      ext.val ≤ tree.max_deposit_amount.val ∧
      (env.accounts env.signer).owner = systemProgram ∧ (env.accounts env.signer).data.isEmpty ∧
      ext.val ≤ (env.balances env.signer).val ∧ env.signer ≠ env.treeToken ∧
      (env.balances env.treeToken).val + ext.val ≤ U64.max ∧
      (fee.val > 0 → fee.val + v.val ≤ U64.max ∧
        (env.balances env.treeToken).val + ext.val ≥ fee.val + v.val ∧
        moveN (fun k => (env.balances k).val) env.signer env.treeToken ext.val.natAbs env.feeRecipient
          + fee.val ≤ U64.max))
    (hW : ext.val < 0 →
      ext.val.natAbs + fee.val + v.val ≤ U64.max ∧
      (env.balances env.treeToken).val ≥ ext.val.natAbs + fee.val + v.val ∧
      (env.balances env.recipient).val + ext.val.natAbs ≤ U64.max ∧
      (fee.val > 0 → payN (fun k => (env.balances k).val) env.treeToken env.recipient ext.val.natAbs
        env.feeRecipient + fee.val ≤ U64.max))
    {p1 p2 : alloc.vec.Vec (Std.Array U8 32#usize)} {t1 t2 : merkle_tree.MerkleTreeAccount}
    (hap1 : merkle_tree.append c.hasher proof.output_commitments.val[0]! tree = ok (.Ok p1, t1))
    (hap2 : merkle_tree.append c.hasher proof.output_commitments.val[1]! t1 = ok (.Ok p2, t2))
    (hnext : tree.next_index.val + 1 ≤ U64.max) :
    transact.transact c.hasher arkFr c.sha256 c.proofVerifier solRuntime env tree config proof
      ext fee recipient feeRecipient out1 out2 ⦃ r => ∃ ap, r.1 = .Ok ap ⦄ := by
  unfold transact.transact
  bstep hroot
  bpos rfl
  bstep hext
  bstep (rfl : arkFr.from_le_bytes_mod_order hsh = ok (leNat hsh : Fr))
  bstep (rfl : arkFr.from_be_bytes_mod_order proof.ext_data_hash = ok (beNat proof.ext_data_hash : Fr))
  bstep (show arkFr.eq (leNat hsh : Fr) (beNat proof.ext_data_hash : Fr) = ok true by
    simp [arkFr, hexteq])
  bpos rfl
  bstep hpub
  bpos rfl
  bstep hfee
  bstep hver
  bpos rfl
  bstep (show solRuntime.rent_exempt_minimum env = ok (.Ok v, env) by simp [solRuntime, hrent])
  have hbnds := i64_bounds ext
  by_cases hpos : ext > 0#i64
  · -- DEPOSIT
    have hposv : ext.val > 0 := i64_pos hpos
    obtain ⟨hlim, hso, hsd, hsle, hsne, hfit, hfeeD⟩ := hD hposv
    bpos hpos
    have hdepv : (IScalar.hcast .U64 ext).val = ext.val.natAbs := by
      rw [IScalar.hcast_val_eq, show UScalarTy.U64.numBits = 64 from rfl,
        Int.emod_eq_of_lt (by omega) (by omega)]; omega
    bstep (rfl : lift (IScalar.hcast .U64 ext) = ok (IScalar.hcast .U64 ext))
    bpos (show IScalar.hcast .U64 ext ≤ tree.max_deposit_amount by
      show (IScalar.hcast .U64 ext).val ≤ tree.max_deposit_amount.val; omega)
    bstep (rfl : lift (IScalar.hcast .U64 ext) = ok (IScalar.hcast .U64 ext))
    obtain ⟨e1, he1⟩ := systemTransfer_ok env env.signer env.treeToken (IScalar.hcast .U64 ext)
      hso hsd (by omega) hsne (by omega)
    bstep (show solRuntime.transfer_from_signer_to_tree_token env (IScalar.hcast .U64 ext)
      = ok (.Ok (), e1) by simp [solRuntime, he1])
    -- the balances after the deposit
    obtain ⟨b1, hb1, rfl⟩ := Option.map_eq_some_iff.mp he1
    obtain ⟨-, -, -, hsb⟩ := stb_spec hb1
    rw [hdepv] at hsb
    by_cases hf : fee > 0#u64
    · have hfv : fee.val > 0 := u64_pos hf
      obtain ⟨hfv1, hge, hfr⟩ := hfeeD hfv
      bpos hf
      bpos (i64_ge0 (by omega))
      obtain ⟨v1, hv1, hv1v⟩ := checked_add_ok fee v hfv1
      bstep (show lift (U64.checked_add fee v) = ok (some v1) by rw [hv1]; rfl)
      have hpool : (b1 env.treeToken).val = (env.balances env.treeToken).val + ext.val.natAbs := by
        have := congrFun hsb env.treeToken
        simp only [moveN, Function.update_self, Function.update_of_ne (Ne.symm hsne)] at this
        exact this
      have hfrv : (b1 env.feeRecipient).val
          = moveN (fun k => (env.balances k).val) env.signer env.treeToken ext.val.natAbs env.feeRecipient :=
        congrFun hsb env.feeRecipient
      bstep (rfl : solRuntime.tree_token_lamports { env with balances := b1 } = ok (b1 env.treeToken))
      bpos (show b1 env.treeToken ≥ v1 by
        show v1.val ≤ (b1 env.treeToken).val; omega)
      bstep (rfl : solRuntime.fee_recipient_lamports { env with balances := b1 } = ok (b1 env.feeRecipient))
      obtain ⟨v2, hv2, -⟩ := checked_sub_ok (b1 env.treeToken) fee (by omega)
      bstep (show lift (U64.checked_sub (b1 env.treeToken) fee) = ok (some v2) by rw [hv2]; rfl)
      obtain ⟨v3, hv3, -⟩ := checked_add_ok (b1 env.feeRecipient) fee (by omega)
      bstep (show lift (U64.checked_add (b1 env.feeRecipient) fee) = ok (some v3) by rw [hv3]; rfl)
      bstep (rfl : solRuntime.set_tree_token_lamports { env with balances := b1 } v2 = ok (.Ok (), _))
      bstep (rfl : solRuntime.set_fee_recipient_lamports _ v3 = ok (.Ok (), _))
      bstep (idx2_ok proof.output_commitments 0#usize (by decide))
      bstep hap1
      bstep (idx2_ok proof.output_commitments 1#usize (by decide))
      bstep hap2
      obtain ⟨w, hw, -⟩ := checked_add_ok tree.next_index 1#u64 (by simpa using hnext)
      bstep (show lift (U64.checked_add tree.next_index 1#u64) = ok (some w) by rw [hw]; rfl)
      exact (WP.spec_ok _).mpr ⟨_, rfl⟩
    · bneg hf
      bstep (idx2_ok proof.output_commitments 0#usize (by decide))
      bstep hap1
      bstep (idx2_ok proof.output_commitments 1#usize (by decide))
      bstep hap2
      obtain ⟨w, hw, -⟩ := checked_add_ok tree.next_index 1#u64 (by simpa using hnext)
      bstep (show lift (U64.checked_add tree.next_index 1#u64) = ok (some w) by rw [hw]; rfl)
      exact (WP.spec_ok _).mpr ⟨_, rfl⟩
  · -- WITHDRAWAL
    bneg hpos
    have hnegv : ext.val < 0 := by have := i64_not_pos hpos; omega
    have hneg : ext < 0#i64 := by scalar_tac
    obtain ⟨hW1, hW2, hW3, hW4⟩ := hW hnegv
    bpos hneg
    obtain ⟨y, hy, hyv⟩ := i64_neg_ok ext hmin
    bstep (show core.num.I64.checked_neg ext = ok (some y) by
      simp only [core.num.I64.checked_neg, hy, Option.ofResult, Result.match.ok])
    bneg (show ¬ y < 0#i64 by intro hc; have := i64_neg hc; omega)
    have habsv : (IScalar.hcast .U64 y).val = ext.val.natAbs := by
      rw [IScalar.hcast_val_eq, hyv, show UScalarTy.U64.numBits = 64 from rfl,
        Int.emod_eq_of_lt (by omega) (by omega)]; omega
    bstep (rfl : lift (IScalar.hcast .U64 y) = ok (IScalar.hcast .U64 y))
    obtain ⟨v2, hv2, hv2v⟩ := checked_add_ok (IScalar.hcast .U64 y) fee (by omega)
    bstep (show lift (U64.checked_add (IScalar.hcast .U64 y) fee) = ok (some v2) by rw [hv2]; rfl)
    obtain ⟨v3, hv3, hv3v⟩ := checked_add_ok v2 v (by omega)
    bstep (show lift (U64.checked_add v2 v) = ok (some v3) by rw [hv3]; rfl)
    bstep (rfl : solRuntime.tree_token_lamports env = ok (env.balances env.treeToken))
    bpos (show env.balances env.treeToken ≥ v3 by
      show v3.val ≤ (env.balances env.treeToken).val; omega)
    bstep (rfl : solRuntime.recipient_lamports env = ok (env.balances env.recipient))
    obtain ⟨v4, hv4, hv4v⟩ := checked_sub_ok (env.balances env.treeToken) (IScalar.hcast .U64 y) (by omega)
    bstep (show lift (U64.checked_sub (env.balances env.treeToken) (IScalar.hcast .U64 y)) = ok (some v4) by
      rw [hv4]; rfl)
    obtain ⟨v5, hv5, hv5v⟩ := checked_add_ok (env.balances env.recipient) (IScalar.hcast .U64 y) (by omega)
    bstep (show lift (U64.checked_add (env.balances env.recipient) (IScalar.hcast .U64 y)) = ok (some v5) by
      rw [hv5]; rfl)
    bstep (rfl : solRuntime.set_tree_token_lamports env v4 = ok (.Ok (), env.setLamports env.treeToken v4))
    bstep (rfl : solRuntime.set_recipient_lamports _ v5 = ok (.Ok (), _))
    have hW' : (fun k => (((env.setLamports env.treeToken v4).setLamports env.recipient v5).balances k).val)
        = payN (fun k => (env.balances k).val) env.treeToken env.recipient ext.val.natAbs := by
      rw [setLamports_vals, setLamports_vals, hv4v, hv5v, habsv]; rfl
    by_cases hf : fee > 0#u64
    · have hfv : fee.val > 0 := u64_pos hf
      have hfr := hW4 hfv
      bpos hf
      bneg (i64_not_ge0 hnegv)
      bstep (rfl : solRuntime.tree_token_lamports _ = ok (((env.setLamports env.treeToken v4).setLamports
        env.recipient v5).balances env.treeToken))
      bstep (rfl : solRuntime.fee_recipient_lamports _ = ok (((env.setLamports env.treeToken v4).setLamports
        env.recipient v5).balances env.feeRecipient))
      have hpt : (((env.setLamports env.treeToken v4).setLamports env.recipient v5).balances env.treeToken).val
          = payN (fun k => (env.balances k).val) env.treeToken env.recipient ext.val.natAbs env.treeToken :=
        congrFun hW' env.treeToken
      have hpf : (((env.setLamports env.treeToken v4).setLamports env.recipient v5).balances env.feeRecipient).val
          = payN (fun k => (env.balances k).val) env.treeToken env.recipient ext.val.natAbs env.feeRecipient :=
        congrFun hW' env.feeRecipient
      have hptv : payN (fun k => (env.balances k).val) env.treeToken env.recipient ext.val.natAbs env.treeToken
          ≥ fee.val := by
        have hb : (env.balances env.treeToken).val ≥ ext.val.natAbs + fee.val + v.val := hW2
        unfold payN
        by_cases hr : env.treeToken = env.recipient
        · rw [← hr, Function.update_self]; dsimp only; omega
        · rw [Function.update_of_ne hr, Function.update_self]; dsimp only; omega
      obtain ⟨v6, hv6, -⟩ := checked_sub_ok _ fee (by rw [hpt]; exact hptv)
      bstep (show lift (_ : Option U64) = ok (some v6) by exact congrArg lift hv6)
      obtain ⟨v7, hv7, -⟩ := checked_add_ok _ fee (by rw [hpf]; exact hfr)
      bstep (show lift (_ : Option U64) = ok (some v7) by exact congrArg lift hv7)
      bstep (rfl : solRuntime.set_tree_token_lamports _ v6 = ok (.Ok (), _))
      bstep (rfl : solRuntime.set_fee_recipient_lamports _ v7 = ok (.Ok (), _))
      bstep (idx2_ok proof.output_commitments 0#usize (by decide))
      bstep hap1
      bstep (idx2_ok proof.output_commitments 1#usize (by decide))
      bstep hap2
      obtain ⟨w, hw, -⟩ := checked_add_ok tree.next_index 1#u64 (by simpa using hnext)
      bstep (show lift (U64.checked_add tree.next_index 1#u64) = ok (some w) by rw [hw]; rfl)
      exact (WP.spec_ok _).mpr ⟨_, rfl⟩
    · bneg hf
      bstep (idx2_ok proof.output_commitments 0#usize (by decide))
      bstep hap1
      bstep (idx2_ok proof.output_commitments 1#usize (by decide))
      bstep hap2
      obtain ⟨w, hw, -⟩ := checked_add_ok tree.next_index 1#u64 (by simpa using hnext)
      bstep (show lift (U64.checked_add tree.next_index 1#u64) = ok (some w) by rw [hw]; rfl)
      exact (WP.spec_ok _).mpr ⟨_, rfl⟩

/-! ## Handler completeness, from the spec's preconditions -/

theorem toPubkey_eq_iff {k u : Pubkey} : toPubkey k = toPubkey u ↔ k = u :=
  ⟨toPubkey_inj, fun h => h ▸ rfl⟩

theorem u64_max_eq : U64.max = 2 ^ 64 - 1 := by simp [U64.max, U64.numBits]

section
set_option linter.unusedSectionVars false
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT]

theorem handler_ok_exists [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree c) (succ : HashesSucceed c) (sys : SyscallsSucceed C) (key : KeyG2Decodes C)
    (a : TransactAccounts) (s₁ : State) (v : U64) (tree : merkle_tree.MerkleTreeAccount)
    (config : admin.GlobalConfig) (spent : Finset LeanSpec.F) (proof : transact.Proof)
    (ext : I64) (fee : U64) (out1 out2 : Slice U8)
    (hshape : TreeShape tree) (hhist : ∀ j : Fin 100, Canonical tree.root_history.val[j.val]!)
    (hsub : ∀ j : Fin 26, Canonical tree.subtrees.val[j.val]!)
    (hd : config.deposit_fee_rate.val ≤ 10000) (hw : config.withdrawal_fee_rate.val ≤ 10000)
    (hm : config.fee_error_margin.val ≤ 10000)
    (hsigner : (s₁ a.signer).owner = systemProgram ∧ (s₁ a.signer).data.isEmpty)
    (hfit : out1.length + out2.length + 120 ≤ Usize.max)
    (hL1 : ext.val ≠ 0) (hA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    LeanSpec.transactPreconditions (toInputs a proof ext fee out1 out2)
      (handlerWorld a s₁ v tree config spent) →
    ∃ ap env' tree', transact.transact c.hasher arkFr c.sha256 c.proofVerifier solRuntime
      (handlerEnv a s₁ v) tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2
      = ok (.Ok ap, env', tree') := by
  intro hpre
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  set inputs := toInputs a proof ext fee out1 out2 with hinputs
  set W := handlerWorld a s₁ v tree config spent with hW
  -- canonical public inputs
  have hcan : ∀ j, j < 7 → Canonical ((publicInputs proof)[j]!) := by
    intro j hj
    exact ((canonicalEncoding_iff _ _).mp (hpre.canonicalInputs ⟨j, hj⟩)).1
  -- the root
  have hroot : merkle_tree.is_known_root tree proof.root = ok true := by
    rw [isKnownRoot_eq tree proof.root hshape hhist]
    have : LeanSpec.rootBytesKnown (toTree tree) (toBytes proof.root.val) := hpre.knownRoot
    simp [this]
  -- the external data hash
  have hlen : (LeanSpec.serealizeExternalData inputs).length ≤ Usize.max := by
    rw [serLength]
    have : inputs.encOut0.length + inputs.encOut1.length = out1.length + out2.length := by
      simp [inputs, toInputs, toBytes, Slice.length]
    omega
  obtain ⟨hsh, hsha⟩ := succ.sha256 (toSlice (LeanSpec.serealizeExternalData inputs))
  have hext : ext_data.calculate_complete_ext_data_hash c.sha256 a.recipient ext out1 out2 fee
      a.feeRecipientAccount transact.SOL_ADDRESS = ok (some hsh) := by
    rw [extDataHash_eq c.sha256 a.recipient a.feeRecipientAccount transact.SOL_ADDRESS ext out1 out2 fee
      inputs rfl rfl rfl rfl rfl rfl rfl hfit, if_pos hpre.encOutLength, hsha, bind_tc_ok]
  have hexteq : (leNat hsh : Fr) = (beNat proof.ext_data_hash : Fr) := by
    have hb := hashes.sha256 _ _ hsha
    rw [toBytes_toSlice _ hlen] at hb
    have h1 : LeanSpec.externalDataHash inputs = inputs.extDataHash := hpre.externalDataBinding
    simp only [LeanSpec.externalDataHash, ← hb, natOfLE_toBytes] at h1
    exact h1
  -- the public amount (L1 excluded)
  have hpub : utils.check_public_amount arkFr ext fee proof.public_amount = ok true := by
    rw [checkPublicAmount_eq]
    have h1 : LeanSpec.pubAmtConsistent ext.val fee.val (toF proof.public_amount) := hpre.pubAmtConsistency
    have h2 : LeanSpec.amountsInRange ext.val fee.val := hpre.amountRange
    simp [h1, h2, hL1]
  -- the fee
  have hfee : utils.validate_fee ext fee config.deposit_fee_rate config.withdrawal_fee_rate
      config.fee_error_margin = ok (.Ok ()) := by
    refine (validateFee_iff ext fee config tree hd hw hm).mpr ⟨?_, hpre.minimumFee⟩
    have h3 : -2^63 < ext.val := hpre.amountRange.1; intro h; rw [h] at h3; norm_num at h3
  -- the proof
  have hver : c.proofVerifier.verify proof = ok true :=
    programVerifier_complete c C laws sys key proof a ext fee out1 out2 hcan hA0 hpre.validZKP
  -- balances, on code addresses
  have hWb : ∀ k, W.balances (toPubkey k) = (s₁ k).lamports.val := by
    intro k; simp [hW, handlerWorld, fromPubkey_toPubkey]
  have hWp : W.state.pool = toPubkey a.treeTokenAccount := rfl
  have hWr : W.nullifierRent = 0 := rfl
  have hu : ∀ k, (s₁ k).lamports.val < 2 ^ 64 := fun k => u64_lt _
  have hmax := u64_max_eq
  obtain ⟨hsP, hAP, htP⟩ := hpre.poolSeparate
  have hsP' : a.signer ≠ a.treeTokenAccount := fun e => hsP (by show toPubkey a.signer = toPubkey a.treeTokenAccount; rw [e])
  have hAP' : ext.val < 0 → a.recipient ≠ a.treeTokenAccount := fun hn e => hAP hn (by show toPubkey a.recipient = toPubkey a.treeTokenAccount; rw [e])
  have htP' : fee.val > 0 → a.feeRecipientAccount ≠ a.treeTokenAccount := fun hf e => htP hf (by show toPubkey a.feeRecipientAccount = toPubkey a.treeTokenAccount; rw [e])
  have hfitB := hpre.balancesFit
  have hsolv := hpre.poolSolvency
  have hsig := hpre.signerSolvency
  have hpubc := hpre.pubAmtConsistency
  have hdelta : ∀ k, LeanSpec.balanceDelta inputs W.state.pool W.nullifierRent (toPubkey k)
      = (if k = a.recipient ∧ ext.val < 0 then (ext.val.natAbs : ℤ) else 0)
        + (if k = a.feeRecipientAccount then (fee.val : ℤ) else 0)
        - (if k = a.signer ∧ ext.val > 0 then ext.val else 0)
        + (if k = a.treeTokenAccount then ext.val - fee.val else 0) := by
    intro k
    simp only [LeanSpec.balanceDelta, hWp, hWr, inputs, toInputs, toPubkey_eq_iff]
    simp
  have hfitk : ∀ k, 0 < LeanSpec.balanceDelta inputs W.state.pool W.nullifierRent (toPubkey k) →
      ((s₁ k).lamports.val : ℤ) + LeanSpec.balanceDelta inputs W.state.pool W.nullifierRent (toPubkey k)
        < 2 ^ 64 := by
    intro k hk; have := hfitB.1 (toPubkey k) hk; rwa [hWb] at this
  have hpoolW : W.poolBalance = (s₁ a.treeTokenAccount).lamports.val := hWb _
  have hsigB : W.balances inputs.s = (s₁ a.signer).lamports.val := hWb _
  have hbnds := i64_bounds ext
  have hfeeb : fee.val < 2 ^ 64 := u64_lt _
  -- DEPOSIT facts
  have hD : ext.val > 0 →
      ext.val ≤ tree.max_deposit_amount.val ∧
      ((handlerEnv a s₁ v).accounts (handlerEnv a s₁ v).signer).owner = systemProgram ∧
      ((handlerEnv a s₁ v).accounts (handlerEnv a s₁ v).signer).data.isEmpty ∧
      ext.val ≤ ((handlerEnv a s₁ v).balances (handlerEnv a s₁ v).signer).val ∧
      (handlerEnv a s₁ v).signer ≠ (handlerEnv a s₁ v).treeToken ∧
      ((handlerEnv a s₁ v).balances (handlerEnv a s₁ v).treeToken).val + ext.val ≤ U64.max ∧
      (fee.val > 0 → fee.val + v.val ≤ U64.max ∧
        ((handlerEnv a s₁ v).balances (handlerEnv a s₁ v).treeToken).val + ext.val ≥ fee.val + v.val ∧
        moveN (fun k => ((handlerEnv a s₁ v).balances k).val) (handlerEnv a s₁ v).signer
          (handlerEnv a s₁ v).treeToken ext.val.natAbs (handlerEnv a s₁ v).feeRecipient
          + fee.val ≤ U64.max) := by
    intro hp
    have hlim : ext.val ≤ ((toConfig config tree).maxDepositLimit : ℤ) := hpre.depositLimit hp
    have hsg0 := hsig
    unfold LeanSpec.signerSolvent at hsg0
    rw [hsigB] at hsg0
    have hsg : (s₁ a.signer).lamports.val ≥ 2 * 0 + (if ext.val > 0 then ext.val.natAbs else 0) := hsg0
    rw [if_pos hp] at hsg
    have hab : ((ext.val.natAbs : ℕ) : ℤ) = ext.val := Int.natAbs_of_nonneg (le_of_lt hp)
    have hpf0 := hfitB.2 hp
    rw [hpoolW] at hpf0
    have hpf : ((s₁ a.treeTokenAccount).lamports.val : ℤ) + ext.val < 2 ^ 64 := hpf0
    show ext.val ≤ tree.max_deposit_amount.val ∧ (s₁ a.signer).owner = systemProgram ∧
      (s₁ a.signer).data.isEmpty ∧ ext.val ≤ (s₁ a.signer).lamports.val ∧ a.signer ≠ a.treeTokenAccount ∧
      ((s₁ a.treeTokenAccount).lamports.val : ℤ) + ext.val ≤ U64.max ∧ _
    refine ⟨by simpa [toConfig] using hlim, hsigner.1, hsigner.2, by omega, hsP', by rw [hmax]; omega,
      fun hf => ?_⟩
    have hps0 := hsolv.2 ⟨le_of_lt hp, hf⟩
    rw [hpoolW] at hps0
    have hps : ((s₁ a.treeTokenAccount).lamports.val : ℤ) + ext.val ≥ fee.val + v.val := hps0
    have hfx : ext.val > (fee.val : ℤ) := hpubc.1 hp
    show fee.val + v.val ≤ U64.max ∧ ((s₁ a.treeTokenAccount).lamports.val : ℤ) + ext.val ≥ fee.val + v.val ∧ _
    refine ⟨by rw [hmax]; omega, by omega, ?_⟩
    show moveN (fun k => (s₁ k).lamports.val) a.signer a.treeTokenAccount ext.val.natAbs
      a.feeRecipientAccount + fee.val ≤ U64.max
    rw [hmax]
    by_cases hts : a.feeRecipientAccount = a.signer
    · rw [hts]
      simp only [moveN, Function.update_of_ne hsP', Function.update_self]
      have := hu a.signer; omega
    · have htp := htP' hf
      simp only [moveN, Function.update_of_ne htp, Function.update_of_ne hts]
      have hn0 : ¬ ext.val < 0 := by omega
      have hk := hfitk a.feeRecipientAccount (by rw [hdelta]; simp [hn0, hts, htp]; omega)
      rw [hdelta] at hk
      simp [hn0, hts, htp] at hk
      omega
  -- WITHDRAWAL facts
  have hWd : ext.val < 0 →
      ext.val.natAbs + fee.val + v.val ≤ U64.max ∧
      ((handlerEnv a s₁ v).balances (handlerEnv a s₁ v).treeToken).val ≥ ext.val.natAbs + fee.val + v.val ∧
      ((handlerEnv a s₁ v).balances (handlerEnv a s₁ v).recipient).val + ext.val.natAbs ≤ U64.max ∧
      (fee.val > 0 → payN (fun k => ((handlerEnv a s₁ v).balances k).val) (handlerEnv a s₁ v).treeToken
        (handlerEnv a s₁ v).recipient ext.val.natAbs (handlerEnv a s₁ v).feeRecipient + fee.val ≤ U64.max) := by
    intro hn
    have hps0 := hsolv.1 hn
    rw [hpoolW] at hps0
    have hps : ((s₁ a.treeTokenAccount).lamports.val : ℤ) ≥ |ext.val| + fee.val + v.val := hps0
    have hab : ((ext.val.natAbs : ℕ) : ℤ) = |ext.val| := Int.natCast_natAbs _
    have hap := hAP' hn
    have hup := hu a.treeTokenAccount
    show ext.val.natAbs + fee.val + v.val ≤ U64.max ∧
      (s₁ a.treeTokenAccount).lamports.val ≥ ext.val.natAbs + fee.val + v.val ∧
      (s₁ a.recipient).lamports.val + ext.val.natAbs ≤ U64.max ∧ _
    have hp0 : ¬ ext.val > 0 := by omega
    have hA := hfitk a.recipient (by rw [hdelta]; simp [hn, hp0, hap]; split <;> omega)
    rw [hdelta] at hA
    simp [hn, hp0, hap] at hA
    refine ⟨by rw [hmax]; omega, by omega, by rw [hmax]; split at hA <;> omega, fun hf => ?_⟩
    show payN (fun k => (s₁ k).lamports.val) a.treeTokenAccount a.recipient ext.val.natAbs
      a.feeRecipientAccount + fee.val ≤ U64.max
    rw [hmax]
    have htp := htP' hf
    unfold payN
    by_cases htA : a.feeRecipientAccount = a.recipient
    · rw [htA, Function.update_self]
      rw [if_pos htA.symm] at hA
      dsimp only; omega
    · rw [Function.update_of_ne htA, Function.update_of_ne htp]
      have hk := hfitk a.feeRecipientAccount (by rw [hdelta]; simp [htA, hp0, htp]; omega)
      rw [hdelta] at hk
      simp [htA, hp0, htp] at hk
      omega
  -- the two appends
  obtain ⟨z, hzb, -⟩ := hashes.zeroBytes
  obtain ⟨z', hzb', hzc⟩ := hashes.zeroBytesCanonical
  rw [hzb] at hzb'; obtain rfl := Result.ok_injective hzb'
  have hroom : tree.next_index.val ≤ 2 ^ 26 - 2 := hpre.treeNotFull
  have hc0 : Canonical proof.output_commitments.val[0]! := by
    simpa [publicInputs] using hcan 5 (by decide)
  have hc1 : Canonical proof.output_commitments.val[1]! := by
    simpa [publicInputs] using hcan 6 (by decide)
  obtain ⟨⟨ra, t1⟩, hr1, p1, hp1, hsub1⟩ := (WP.spec_equiv_exists _ _).mp
    (append_complete c.hasher hashes.poseidonCanonical succ.poseidon z hzb hzc _ tree hshape
      (by omega) (fun i hi => hsub ⟨i, hi⟩) hc0)
  simp only at hp1 hsub1; subst hp1
  obtain ⟨hsh1, -, hidx1, -⟩ := append_shape _ _ tree t1 p1 hshape hr1
  obtain ⟨⟨rb, t2⟩, hr2, p2, hp2, -⟩ := (WP.spec_equiv_exists _ _).mp
    (append_complete c.hasher hashes.poseidonCanonical succ.poseidon z hzb hzc _ t1 hsh1
      (by omega) hsub1 hc1)
  simp only at hp2; subst hp2
  have hmin : ext.val ≠ -9223372036854775808 := by
    have h3 : -2^63 < ext.val := hpre.amountRange.1; omega
  obtain ⟨⟨r, e', t'⟩, hres, ap, hap⟩ := (WP.spec_equiv_exists _ _).mp
    (handler_complete_code c (handlerEnv a s₁ v) tree config proof ext fee a.recipient a.feeRecipientAccount
      out1 out2 hsh v hroot hext hexteq hpub hfee hver rfl hL1 hmin hD hWd hr1 hr2
      (by rw [hmax]; omega))
  simp only at hap; subst hap
  exact ⟨ap, e', t', hres⟩


/-- **Handler completeness, exact version.** -/
theorem handler_complete_exact' [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree c) (succ : HashesSucceed c) (sys : SyscallsSucceed C) (key : KeyG2Decodes C)
    (a : TransactAccounts) (s₁ : State) (v : U64) (tree : merkle_tree.MerkleTreeAccount)
    (config : admin.GlobalConfig) (spent : Finset LeanSpec.F) (proof : transact.Proof)
    (ext : I64) (fee : U64) (out1 out2 : Slice U8)
    (hshape : TreeShape tree) (hhist : ∀ j : Fin 100, Canonical tree.root_history.val[j.val]!)
    (hsub : ∀ j : Fin 26, Canonical tree.subtrees.val[j.val]!)
    (hd : config.deposit_fee_rate.val ≤ 10000) (hw : config.withdrawal_fee_rate.val ≤ 10000)
    (hm : config.fee_error_margin.val ≤ 10000)
    (hsigner : (s₁ a.signer).owner = systemProgram ∧ (s₁ a.signer).data.isEmpty)
    (hfit : out1.length + out2.length + 120 ≤ Usize.max)
    (hL1 : ext.val ≠ 0) (hA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof ext fee out1 out2
    let W := handlerWorld a s₁ v tree config spent
    LeanSpec.transactPreconditions inputs W →
    ∃ ap env' tree', transact.transact c.hasher arkFr c.sha256 c.proofVerifier solRuntime
      (handlerEnv a s₁ v) tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2
      = ok (.Ok ap, env', tree') ∧
      (∀ k, (env'.balances k).val = (LeanSpec.transactEffects inputs W).balances (toPubkey k)) ∧
      toTree tree' = (LeanSpec.transactEffects inputs W).state.tree := by
  intro inputs W hpre
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  obtain ⟨ap, e', t', hres⟩ := handler_ok_exists c C laws hashes succ sys key a s₁ v tree config spent
    proof ext fee out1 out2 hshape hhist hsub hd hw hm hsigner hfit hL1 hA0 hpre
  have hok := handler_ok c (handlerEnv a s₁ v) tree config proof ext fee a.recipient a.feeRecipientAccount
    out1 out2 ap e' t' hres
  refine ⟨ap, e', t', hres, ?_, ?_⟩
  · -- balances
    obtain ⟨v', hv', hdep, hwd, -⟩ := hok.rent
    obtain ⟨hsP, hAP, htP⟩ := hpre.poolSeparate
    have htP' : fee.val > 0 → a.feeRecipientAccount ≠ a.treeTokenAccount := fun hf e =>
      htP hf (by show toPubkey a.feeRecipientAccount = toPubkey a.treeTokenAccount; rw [e])
    have hAP' : ext.val < 0 → a.recipient ≠ a.treeTokenAccount := fun hn e =>
      hAP hn (by show toPubkey a.recipient = toPubkey a.treeTokenAccount; rw [e])
    have hfeeOk : a.feeRecipientAccount ≠ a.treeTokenAccount ∨ fee.val = 0 := by
      by_cases hf : fee.val > 0
      · exact Or.inl (htP' hf)
      · exact Or.inr (by omega)
    set B : Pubkey → ℕ := fun k => (s₁ k).lamports.val with hB
    have hWb : W.balances = fun x => B (fromPubkey x) := rfl
    have hpool : W.state.pool = toPubkey a.treeTokenAccount := rfl
    have hnr : W.nullifierRent = 0 := rfl
    have hext' : inputs.extAmt ≠ 0 := hL1
    set Q : Pubkey → ℕ := Function.update B a.signer (B a.signer - 2 * 0) with hQdef
    have hQ : Q = B := by simp [hQdef]
    have hspec : (LeanSpec.transactEffects inputs W).balances = fun x => moveN
        (if ext.val > 0 then moveN Q a.signer a.treeTokenAccount ext.val.natAbs
          else moveN Q a.treeTokenAccount a.recipient ext.val.natAbs)
        a.treeTokenAccount a.feeRecipientAccount fee.val (fromPubkey x) := by
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
        if_neg hext', hWb, hpool, hnr]
      have hs : inputs.s = toPubkey a.signer := rfl
      have hA : inputs.A = toPubkey a.recipient := rfl
      have ht : inputs.t = toPubkey a.feeRecipientAccount := rfl
      have hf : inputs.f = fee.val := rfl
      have he : inputs.extAmt = ext.val := rfl
      rw [hs, hA, ht, hf, he, fromPubkey_toPubkey, ← update_fromPubkey]
      split
      · rw [moveLamports_fromPubkey, moveLamports_fromPubkey]
      · rw [moveLamports_fromPubkey, moveLamports_fromPubkey]
    intro k
    rw [hspec]
    simp only [fromPubkey_toPubkey, hQ]
    by_cases hp : ext.val > 0
    · have he : (fun k => (e'.balances k).val) = payN (moveN B a.signer a.treeTokenAccount
          ext.val.natAbs) a.treeTokenAccount a.feeRecipientAccount fee.val := (hdep hp).2.2.2.2
      rw [show (e'.balances k).val = _ from congrFun he k, payN_eq_moveN _ _ _ _ hfeeOk, if_pos hp]
    · have hn : ext.val < 0 := by omega
      have he : (fun k => (e'.balances k).val) = payN (payN B a.treeTokenAccount a.recipient
          ext.val.natAbs) a.treeTokenAccount a.feeRecipientAccount fee.val := (hwd hn).2
      rw [show (e'.balances k).val = _ from congrFun he k, payN_eq_moveN _ _ _ _ hfeeOk,
        payN_eq_moveN _ _ _ _ (Or.inl (hAP' hn)), if_neg hp]
  · -- the tree
    obtain ⟨p1, p2, t1, hap1, hap2⟩ := hok.appends
    obtain ⟨hT1, hsh1, -⟩ := append_ok' c hashes _ tree t1 p1 hshape hap1
    obtain ⟨hT2, -⟩ := append_ok' c hashes _ t1 t' p2 hsh1 hap2
    have hext' : inputs.extAmt ≠ 0 := hL1
    simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, LeanSpec.nullifierRentEffects,
      if_neg hext']
    rw [hT2, hT1]
    rfl
end

end Connection
