import proofs.VerifyProof.Accumulate
open Aeneas Aeneas.Std Result ControlFlow

/-! # `fv_verify_proof_full_entry`: soundness direction

`fv_verify_proof_full_entry_sound`: if the verifier returns `true`, then
1. all seven public inputs, read as big-endian integers `kᵢ`, are below r;
2. all eight verifying-key IC entries decode to G1 points;
3. proof B and C and the key's α, β, γ, δ decode, and for some G1 point A,
     e(A, B) · e(vk_x, γ) · e(C, δ) · e(α, β) = 1,   where vk_x = IC₀ + Σᵢ kᵢ · ICᵢ₊₁.

That is the Groth16 verification equation, rearranged the way the program checks it.
Because of (1), each kᵢ already is its value mod r -- no reduction is hidden in the statement.

Assumes only the syscall contracts, `curve_shim.AltBn128Syscalls`. It does NOT say:
- that A is the negation of the point in `proof_a_raw`. The program decodes and negates A with
  its own arkworks code (`G1Shim`), and nothing relates that decoder to the syscall's yet.
  B and C, which are passed through untouched, are pinned to their bytes.
- that valid proofs are accepted (completeness).
- anything about the spec's groups or `Groth16.verify`: that is the bridge, and needs
  bilinearity, which the contracts deliberately do not assume. -/

namespace zkcash

set_option hygiene false in
/-- Split the first `let x ← m` off hypothesis `h : (do ...) = ok v`, consuming `h`. -/
local macro "peel " pat:Lean.Parser.Tactic.rcasesPatMed : tactic =>
  `(tactic| (replace h := (bind_eq_ok _ _ _).mp h; obtain $pat := h))

variable {G1 G2 GT : Type} [AddCommMonoid G1] [CommMonoid GT] [S : curve_shim.AltBn128Syscalls G1 G2 GT]

/-- The seven public inputs, in the order `fv_verify_proof_full_entry` places them. -/
def verifierInputs (proof_root proof_public_amount proof_ext_data_hash : Array Std.U8 32#usize)
    (proof_input_nullifiers proof_output_commitments : Array (Array Std.U8 32#usize) 2#usize) :
    List (Array Std.U8 32#usize) :=
  [proof_root, proof_public_amount, proof_ext_data_hash,
   proof_input_nullifiers.val[0]!, proof_input_nullifiers.val[1]!,
   proof_output_commitments.val[0]!, proof_output_commitments.val[1]!]

/-- If the verifier accepts, the inputs are in range and the Groth16 pairing equation holds
    for the decoded key and some proof points; see the module header for what is not claimed. -/
theorem fv_verify_proof_full_entry_sound
    (proof_root proof_public_amount proof_ext_data_hash : Array Std.U8 32#usize)
    (proof_input_nullifiers proof_output_commitments : Array (Array Std.U8 32#usize) 2#usize)
    (proof_a_raw : Array Std.U8 64#usize) (proof_b : Array Std.U8 128#usize) (proof_c : Array Std.U8 64#usize)
    (vk_alpha_g1 : Array Std.U8 64#usize) (vk_beta_g2 vk_gamme_g2 vk_delta_g2 : Array Std.U8 128#usize)
    (vk_ic : Array (Array Std.U8 64#usize) 8#usize)
    (h : utils.fv_verify_proof_full_entry proof_root proof_public_amount proof_ext_data_hash
      proof_input_nullifiers proof_output_commitments proof_a_raw proof_b proof_c
      vk_alpha_g1 vk_beta_g2 vk_gamme_g2 vk_delta_g2 vk_ic = ok true) :
    let inputs := verifierInputs proof_root proof_public_amount proof_ext_data_hash
      proof_input_nullifiers proof_output_commitments
    (∀ j : ℕ, j < 7 → curve_shim.natOfBE (inputs[j]!) < bn254_r) ∧
    (∀ j : ℕ, j < 8 → S.decodeG1 (vk_ic.val[j]!) = some (ic S vk_ic j)) ∧
    ∃ (A : G1) (B : G2) (C α : G1) (β γ δ : G2),
      S.decodeG2 proof_b = some B ∧ S.decodeG1 proof_c = some C ∧
      S.decodeG1 vk_alpha_g1 = some α ∧ S.decodeG2 vk_beta_g2 = some β ∧
      S.decodeG2 vk_gamme_g2 = some γ ∧ S.decodeG2 vk_delta_g2 = some δ ∧
      S.pairing A B *
        S.pairing (ic S vk_ic 0 + ∑ j ∈ Finset.range 7, curve_shim.natOfBE (inputs[j]!) • ic S vk_ic (j + 1)) γ *
        S.pairing C δ * S.pairing α β = 1 := by
  intro inputs
  -- Walk through the function, naming the result of every step.
  -- public_inputs_vec, filled in order
  simp only [utils.fv_verify_proof_full_entry, bind_eq_ok] at h
  obtain ⟨pv1, hpv1, pv2, hpv2, pv3, hpv3, a1, ha1, pv4, hpv4, a2, ha2, pv5, hpv5, a3, ha3, pv6, hpv6,
    a4, ha4, im, him, h⟩ := h
  -- proof A: decode, negate, re-encode (G1Shim); decoding must succeed
  peel ⟨a_be, ha_be, h⟩
  peel ⟨o, ho, h⟩
  rcases o with _ | point
  · simp at h
  peel ⟨gs, hgs, h⟩
  peel ⟨proof_a_neg, _, h⟩
  peel ⟨proof_a, _, h⟩
  -- the length check must pass
  peel ⟨s, hs, h⟩
  peel ⟨i1, hi1, h⟩
  peel ⟨s1, hs1, h⟩
  split at h
  · simp at h
  -- the accumulation loop must report ok
  peel ⟨prep, hprep, h⟩
  peel ⟨⟨prep1, ok1⟩, hloop, h⟩
  cases ok1
  · simp at h
  -- the eight copies into pairing_input
  peel ⟨pi1, hpi1, h⟩
  peel ⟨off, hoff, h⟩
  peel ⟨pi2, hpi2, h⟩
  peel ⟨off1, hoff1, h⟩
  peel ⟨pi3, hpi3, h⟩
  peel ⟨off2, hoff2, h⟩
  peel ⟨pi4, hpi4, h⟩
  peel ⟨off3, hoff3, h⟩
  peel ⟨pi5, hpi5, h⟩
  peel ⟨off4, hoff4, h⟩
  peel ⟨pi6, hpi6, h⟩
  peel ⟨off5, hoff5, h⟩
  peel ⟨pi7, hpi7, h⟩
  peel ⟨off6, hoff6, h⟩
  peel ⟨pi8, hpi8, h⟩
  -- the pairing syscall must answer, with last byte 1
  peel ⟨o1, ho1, h⟩
  rcases o1 with _ | res
  · simp at h
  peel ⟨i3, hi3, h⟩
  split at h
  · simp at h
  rename_i hne
  -- the offsets
  have e0 : off.val = 64 := by have := add_ok_val (by scalar_tac) hoff; simpa using this
  have e1 : off1.val = 192 := by have := add_ok_val (by scalar_tac) hoff1; simp at this; omega
  have e2 : off2.val = 256 := by have := add_ok_val (by scalar_tac) hoff2; simp at this; omega
  have e3 : off3.val = 384 := by have := add_ok_val (by scalar_tac) hoff3; simp at this; omega
  have e4 : off4.val = 448 := by have := add_ok_val (by scalar_tac) hoff4; simp at this; omega
  have e5 : off5.val = 576 := by have := add_ok_val (by scalar_tac) hoff5; simp at this; omega
  have e6 : off6.val = 640 := by have := add_ok_val (by scalar_tac) hoff6; simp at this; omega
  -- what each pairing copy loop wrote
  have hq1 := post_of_ok (loop1_spec proof_a _) hpi1
  have hq2 := post_of_ok (loop2_spec proof_b pi1 off (by omega)) hpi2
  have hq3 := post_of_ok (loop3_spec prep1 pi2 off1 (by omega)) hpi3
  have hq4 := post_of_ok (loop4_spec vk_gamme_g2 pi3 off2 (by omega)) hpi4
  have hq5 := post_of_ok (loop5_spec proof_c pi4 off3 (by omega)) hpi5
  have hq6 := post_of_ok (loop6_spec vk_delta_g2 pi5 off4 (by omega)) hpi6
  have hq7 := post_of_ok (loop7_spec vk_alpha_g1 pi6 off5 (by omega)) hpi7
  have hq8 := post_of_ok (loop8_spec vk_beta_g2 pi7 off6 (by omega)) hpi8
  -- so the eight slices of the pairing input are exactly the proof and key elements
  have eB : curve_shim.bytesAt pi8 64 128#usize (by scalar_tac) = proof_b := by
    apply bytesAt_eq; intro j hj
    have hj : j < 128 := by simpa using hj
    rw [hq8, if_neg (by omega), hq7, if_neg (by omega), hq6, if_neg (by omega), hq5, if_neg (by omega), hq4, if_neg (by omega), hq3, if_neg (by omega), hq2, if_pos (by omega)]
    congr 1; omega
  have eP : curve_shim.bytesAt pi8 192 64#usize (by scalar_tac) = prep1 := by
    apply bytesAt_eq; intro j hj
    have hj : j < 64 := by simpa using hj
    rw [hq8, if_neg (by omega), hq7, if_neg (by omega), hq6, if_neg (by omega), hq5, if_neg (by omega), hq4, if_neg (by omega), hq3, if_pos (by omega)]
    congr 1; omega
  have eG : curve_shim.bytesAt pi8 256 128#usize (by scalar_tac) = vk_gamme_g2 := by
    apply bytesAt_eq; intro j hj
    have hj : j < 128 := by simpa using hj
    rw [hq8, if_neg (by omega), hq7, if_neg (by omega), hq6, if_neg (by omega), hq5, if_neg (by omega), hq4, if_pos (by omega)]
    congr 1; omega
  have eC : curve_shim.bytesAt pi8 384 64#usize (by scalar_tac) = proof_c := by
    apply bytesAt_eq; intro j hj
    have hj : j < 64 := by simpa using hj
    rw [hq8, if_neg (by omega), hq7, if_neg (by omega), hq6, if_neg (by omega), hq5, if_pos (by omega)]
    congr 1; omega
  have eD : curve_shim.bytesAt pi8 448 128#usize (by scalar_tac) = vk_delta_g2 := by
    apply bytesAt_eq; intro j hj
    have hj : j < 128 := by simpa using hj
    rw [hq8, if_neg (by omega), hq7, if_neg (by omega), hq6, if_pos (by omega)]
    congr 1; omega
  have eAl : curve_shim.bytesAt pi8 576 64#usize (by scalar_tac) = vk_alpha_g1 := by
    apply bytesAt_eq; intro j hj
    have hj : j < 64 := by simpa using hj
    rw [hq8, if_neg (by omega), hq7, if_pos (by omega)]
    congr 1; omega
  have eBe : curve_shim.bytesAt pi8 640 128#usize (by scalar_tac) = vk_beta_g2 := by
    apply bytesAt_eq; intro j hj
    have hj : j < 128 := by simpa using hj
    rw [hq8, if_pos (by omega)]
    congr 1; omega
  -- the pairing syscall answered 1
  have hr := post_of_ok (Array.index_usize_spec res 31#usize (by scalar_tac)) hi3
  have hi3' : i3 = 1#u8 := UScalar.eq_of_val_eq (by simpa using hne)
  have h31 : res.val[31]! = 1#u8 := by rw [← hi3', hr, getElem_eq_getElem!]; rfl
  obtain ⟨P₁, P₂, P₃, P₄, Q₁, Q₂, Q₃, Q₄, -, h2, h3, h4, h5, h6, h7, h8, heq⟩ :=
    S.pairing_spec pi8 res ho1 h31
  rw [eB] at h2; rw [eP] at h3; rw [eG] at h4; rw [eC] at h5; rw [eD] at h6; rw [eAl] at h7; rw [eBe] at h8
  -- the public-input array holds the seven inputs, in order
  rcases im with ⟨x6, back⟩
  obtain ⟨-, hback⟩ := post_of_ok (Array.index_mut_usize_spec pv6 6#usize (by scalar_tac)) him
  have hv1 := post_of_ok (Array.update_spec _ 0#usize proof_root (by scalar_tac)) hpv1
  have hv2 := post_of_ok (Array.update_spec _ 1#usize proof_public_amount (by scalar_tac)) hpv2
  have hv3 := post_of_ok (Array.update_spec _ 2#usize proof_ext_data_hash (by scalar_tac)) hpv3
  have hv4 := post_of_ok (Array.update_spec _ 3#usize a1 (by scalar_tac)) hpv4
  have hv5 := post_of_ok (Array.update_spec _ 4#usize a2 (by scalar_tac)) hpv5
  have hv6 := post_of_ok (Array.update_spec _ 5#usize a3 (by scalar_tac)) hpv6
  have hb1 := post_of_ok (Array.index_usize_spec proof_input_nullifiers 0#usize (by scalar_tac)) ha1
  have hb2 := post_of_ok (Array.index_usize_spec proof_input_nullifiers 1#usize (by scalar_tac)) ha2
  have hb3 := post_of_ok (Array.index_usize_spec proof_output_commitments 0#usize (by scalar_tac)) ha3
  have hb4 := post_of_ok (Array.index_usize_spec proof_output_commitments 1#usize (by scalar_tac)) ha4
  rw [getElem_eq_getElem!] at hb1 hb2 hb3 hb4
  have hinputs : (back a4).val = inputs := by
    subst hback hv6 hv5 hv4 hv3 hv2 hv1 hb1 hb2 hb3 hb4
    rfl
  -- the accumulation loop
  change utils.fv_verify_proof_full_entry_loop0 vk_ic (back a4) prep true 0#usize = ok (prep1, true) at hloop
  have hprep' := post_of_ok (Array.index_usize_spec vk_ic 0#usize (by scalar_tac)) hprep
  rw [getElem_eq_getElem!] at hprep'
  subst hprep'
  obtain ⟨hall, acc, hacc, hprep1⟩ :=
    loop0_sound (S := S) vk_ic (back a4) 7 0#usize _ prep1 (by simp) (by simp) hloop
  have hacc0 : S.decodeG1 (vk_ic.val[0]!) = some acc := hacc
  have hic0 : ic S vk_ic 0 = acc := by simp only [ic, hacc0, Option.getD_some]
  have hvkx : ic S vk_ic 0 + ∑ j ∈ Finset.range 7, curve_shim.natOfBE (inputs[j]!) • ic S vk_ic (j + 1) = P₂ := by
    rw [h3, Option.some.injEq] at hprep1
    rw [hprep1, ← hinputs, Finset.range_eq_Ico, hic0]
    rfl
  refine ⟨fun j hj => ?_, fun j hj => ?_, P₁, Q₁, P₃, P₄, Q₄, Q₂, Q₃, h2, h5, h7, h8, h4, h6, ?_⟩
  · rw [← hinputs]; exact (hall j (by simp) hj).1
  · rcases j with _ | j
    · rw [hacc0, hic0]
    · exact (hall j (by simp) (by omega)).2
  · rw [hvkx]; exact heq
