/-
The program's Groth16 verifier checks the Groth16 equation.

`verify_proof_groth16` / `programVerifier_groth16`: if the extracted
`zkcash_core::groth16::verify_proof` accepts a proof, then its seven public
inputs (read big-endian, in circuit order) are below r, the key's and the
proof's points decode, and, with A the point in `proof_a`,
`e(-A, B) · e(vk_x, γ) · e(C, δ) · e(α, β) = 1` where
`vk_x = IC₀ + Σ kⱼ · ICⱼ₊₁`. It assumes only the `alt_bn128` syscall
contracts (`AltBn128Contracts`, Model/Bn254.lean). It rules out the verifier
checking the wrong equation: a swapped key element, a wrong IC index, a
missing range check, a wrong pairing layout.

`groth16Sound_of_equation` then derives the model's `Groth16Sound` from
Groth16 soundness for the program's key alone (`Groth16EquationSound`).

Adapted from `formal-verification/lean/proofs/VerifyProof` (Verified Privacy
Cash: the statement and the proof's structure), here proven about the code
the program runs, with the field-size check and G1 negation proven rather
than assumed.
-/
import PrivacyCash.Model.Bn254
import PrivacyCash.Model.Field
import PrivacyCash.Model.Crypto
import PrivacyCash.Proofs.G1
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Proofs.Groth16
open zkcash_core PrivacyCash.Model PrivacyCash.Proofs.G1

/-- Byte `j` of `out` after copying the first `i` bytes of `bytes` to offset `off`. -/
def copied (out : Std.Array U8 768#usize) (off : Nat) (bytes : List U8) (i j : Nat) : U8 :=
  if off ≤ j ∧ j < off + i then bytes[j - off]! else out.val[j]!

@[step]
theorem copy_into_spec {N : Usize} (out : Std.Array U8 768#usize) (off : Usize)
    (bytes : Std.Array U8 N) (h : off.val + N.val ≤ 768) :
    groth16.copy_into out off bytes ⦃ r =>
      ∀ j, j < 768 → r.val[j]! = copied out off.val bytes.val N.val j ⦄ := by
  unfold groth16.copy_into groth16.copy_into_loop
  apply loop.spec_decr_nat (fun (x : Std.Array U8 768#usize × Usize) => N.val - x.2.val)
    (fun x => x.2.val ≤ N.val ∧ ∀ j, j < 768 → x.1.val[j]! = copied out off.val bytes.val x.2.val j)
  · rintro ⟨cur, i⟩ ⟨hi, hcur⟩
    dsimp only at hi hcur ⊢
    unfold groth16.copy_into_loop.body
    split
    · rename_i hlt
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      intro j hj
      rw [a_post, Std.Array.set_val_eq]
      have hcj := hcur j hj
      simp only [copied, List.getElem!_eq_getElem?_getD, List.getElem?_set] at hcj ⊢
      by_cases hji : i2.val = j
      · subst hji
        have hlt' : i.val < N.val := by scalar_tac
        have hoff : i2.val - off.val = i.val := by scalar_tac
        rw [if_pos (by scalar_tac), hoff, i1_post,
          List.getElem?_eq_getElem (by simp; exact hlt')]
        split_ifs <;> first | rfl | (exfalso; scalar_tac)
      · simp only [hji, if_false]
        rw [hcj]
        split_ifs <;> first | rfl | (exfalso; scalar_tac)
    · rename_i hge
      simp only [WP.spec_ok]
      intro j hj
      rw [hcur j hj]
      have : i.val = N.val := by scalar_tac
      simp only [copied, this]
  · refine ⟨by simp, fun j hj => ?_⟩
    simp [copied]

/-! ## Big-endian numbers -/

/-- Bytes read as a big-endian number. -/
def bn (l : List U8) : Nat := l.foldl (fun acc x => acc * 256 + x.val) 0

theorem foldl_acc (l : List U8) (acc : Nat) :
    l.foldl (fun acc x => acc * 256 + x.val) acc = acc * 256 ^ l.length + bn l := by
  induction l generalizing acc with
  | nil => simp [bn]
  | cons x t ih =>
    simp only [List.foldl_cons, bn, List.length_cons]
    rw [ih, ih (0 * 256 + x.val)]
    ring

theorem bn_append (l₁ l₂ : List U8) : bn (l₁ ++ l₂) = bn l₁ * 256 ^ l₂.length + bn l₂ := by
  rw [bn, List.foldl_append, foldl_acc]; rfl

theorem bn_lt (l : List U8) : bn l < 256 ^ l.length := by
  induction l using List.reverseRecOn with
  | nil => simp [bn]
  | append_singleton t x ih =>
    rw [bn_append]
    have hx : x.val < 256 := by have := x.hBounds; simpa using this
    simp only [bn, List.foldl_cons, List.foldl_nil, List.length_append, List.length_singleton, pow_succ] at *
    nlinarith

theorem bn_cons (x : U8) (s : List U8) : bn (x :: s) = x.val * 256 ^ s.length + bn s := by
  have := bn_append [x] s
  simpa [bn] using this

/-- The first differing byte decides the comparison. -/
theorem bn_lt_iff_of_first_diff (p s₁ s₂ : List U8) (x y : U8) (hlen : s₁.length = s₂.length)
    (hne : x ≠ y) : bn (p ++ x :: s₁) < bn (p ++ y :: s₂) ↔ x.val < y.val := by
  rw [bn_append, bn_append, bn_cons, bn_cons, List.length_cons, List.length_cons, hlen]
  have h1 := bn_lt s₁
  have h2 := bn_lt s₂
  rw [hlen] at h1
  have hxy : x.val ≠ y.val := fun h => hne (UScalar.eq_of_val_eq h)
  set n := s₂.length
  have hpos : 0 < 256 ^ n := by positivity
  constructor
  · intro h
    by_contra hge
    have : y.val + 1 ≤ x.val := by omega
    have : (y.val + 1) * 256 ^ n ≤ x.val * 256 ^ n := Nat.mul_le_mul_right _ this
    nlinarith
  · intro h
    have : (x.val + 1) * 256 ^ n ≤ y.val * 256 ^ n := Nat.mul_le_mul_right _ h
    nlinarith

theorem beNatOf_eq {n : Usize} (b : Std.Array U8 n) : beNatOf b = bn b.val := rfl

/-- The modulus constant in the code is r. -/
theorem modulus_be : bn utils.BN254_FR_MODULUS_BE.val = bn254ScalarModulus := by
  simp only [utils.BN254_FR_MODULUS_BE, bn254ScalarModulus]
  decide

/-! ## Syscall inputs -/

theorem bytesAt_concat_left {m n k : Usize} (a : Std.Array U8 m) (b : Std.Array U8 n)
    (h : m.val + n.val = k.val) (h' : 0 + m.val ≤ k.val) :
    bytesAt (concatArrays a b h) 0 m h' = a := by
  rw [Std.Array.eq_iff]
  simp [bytesAt, concatArrays]

theorem bytesAt_concat_right {m n k : Usize} (a : Std.Array U8 m) (b : Std.Array U8 n)
    (h : m.val + n.val = k.val) (off : Nat) (hoff : off = m.val) (h' : off + n.val ≤ k.val) :
    bytesAt (concatArrays a b h) off n h' = b := by
  subst hoff
  rw [Std.Array.eq_iff]
  simp [bytesAt, concatArrays]

/-! ## The field-size check -/

/-- `is_less_than_bn254_field_size_be(bytes)`: the bytes, read big-endian, are below r.
    (The code compares byte by byte with the modulus; this proves that is the
    numeric comparison.) -/
@[step]
theorem is_less_than_bn254_field_size_be_spec (b : Std.Array U8 32#usize) :
    utils.is_less_than_bn254_field_size_be b ⦃ r => r = decide (beNatOf b < bn254ScalarModulus) ⦄ := by
  rw [beNatOf_eq, ← modulus_be]
  unfold utils.is_less_than_bn254_field_size_be utils.is_less_than_bn254_field_size_be_loop
  apply loop.spec_decr_nat (fun (i : Usize) => 32 - i.val)
    (fun i => i.val ≤ 32 ∧ b.val.take i.val = utils.BN254_FR_MODULUS_BE.val.take i.val)
  · rintro i ⟨hi, hpre⟩
    unfold utils.is_less_than_bn254_field_size_be_loop.body
    split
    · rename_i hlt
      have hi32 : i.val < 32 := by scalar_tac
      have hbl : b.val.length = 32 := by simp
      have hml : utils.BN254_FR_MODULUS_BE.val.length = 32 := by simp
      -- `l = take i l ++ l[i] :: drop (i + 1) l`
      have split_at : ∀ l : List U8, (h : i.val < l.length) →
          l = l.take i.val ++ l[i.val] :: l.drop (i.val + 1) := fun l h => by
        rw [← List.drop_eq_getElem_cons h, List.take_append_drop]
      step*
      · -- the bytes differ: they decide the comparison
        rename_i hne
        have hne' : i1 ≠ i2 := by simpa using hne
        rw [split_at b.val (by omega), split_at utils.BN254_FR_MODULUS_BE.val (by omega), hpre]
        simp only [decide_eq_decide]
        rw [bn_lt_iff_of_first_diff _ _ _ _ _ (by simp) (by rw [← i1_post, ← i2_post]; exact hne'),
          ← i1_post, ← i2_post]
        exact Iff.rfl
      · -- the bytes agree: the common prefix grows by one
        rename_i heq
        have heq' : i1 = i2 := UScalar.eq_of_val_eq (by simpa using heq)
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [show i3.val = i.val + 1 by scalar_tac, List.take_add_one, List.take_add_one, hpre,
          List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega), ← i1_post, ← i2_post, heq']
    · -- all 32 bytes agree: the number is r, which is not below r
      rename_i hge
      have hi : i.val = 32 := by scalar_tac
      simp only [WP.spec_ok]
      have hb : b.val = utils.BN254_FR_MODULUS_BE.val := by
        have := hpre
        rwa [hi, List.take_of_length_le (by simp), List.take_of_length_le (by simp)] at this
      simp [hb]
  · exact ⟨by simp, by simp⟩

/-! ## `prepare_inputs`: `vk_x = IC₀ + Σ kⱼ · ICⱼ₊₁` -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT] {s : AltBn128}
  (C : AltBn128Contracts s G1 G2 GT)

/-- The point the key's `j`-th IC entry decodes to (0 if it does not; the
    lemmas below also show it decodes). -/
def ic (vk : groth16.VerifyingKey) (j : Nat) : G1 := (C.decodeG1 (vk.vk_ic.val[j]!)).getD 0

/-- The public inputs as the program reads them: big-endian integers. -/
def k (pub : Std.Array (Std.Array U8 32#usize) 7#usize) (j : Nat) : Nat := beNatOf (pub.val[j]!)

/-- `vk_x` after the first `i` inputs. -/
def vkx (vk : groth16.VerifyingKey) (pub : Std.Array (Std.Array U8 32#usize) 7#usize) (i : Nat) : G1 :=
  ic C vk 0 + ∑ j ∈ Finset.range i, k pub j • ic C vk (j + 1)

theorem prepare_inputs_spec (pub : Std.Array (Std.Array U8 32#usize) 7#usize)
    (vk : groth16.VerifyingKey) :
    groth16.prepare_inputs (solanaBn254 s) pub vk ⦃ r => ∀ p, r = .Ok p →
      (∀ j, j < 7 → k pub j < bn254ScalarModulus) ∧
      (∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) = some (ic C vk j)) ∧
      C.decodeG1 p = some (vkx C vk pub 7) ⦄ := by
  unfold groth16.prepare_inputs
  step*
  unfold groth16.prepare_inputs_loop
  apply loop.spec_decr_nat (fun (x : Std.Array U8 64#usize × Usize) => 7 - x.2.val)
    (fun x => x.2.val ≤ 7 ∧ (∀ j, j < x.2.val → k pub j < bn254ScalarModulus) ∧
      (x.2.val = 0 → x.1 = vk.vk_ic.val[0]!) ∧
      (0 < x.2.val → (∀ j, j ≤ x.2.val → C.decodeG1 (vk.vk_ic.val[j]!) = some (ic C vk j)) ∧
        C.decodeG1 x.1 = some (vkx C vk pub x.2.val)))
  · rintro ⟨prep, i⟩ ⟨hi, hk, h0, hpos⟩
    dsimp only at hi hk h0 hpos ⊢
    unfold groth16.prepare_inputs_loop.body
    split
    · simp only [solanaBn254]
      rename_i hlt
      have hi7 : i.val < 7 := by simp [groth16.NR_PUBLIC_INPUTS] at hlt; scalar_tac
      step*
      · -- one step: k_i · IC_{i+1} is added to the running sum
        have hb : b = true := ‹b = true›
        have hmul := ‹s.multiplication _ = some p›
        have hadd := ‹s.addition _ = some p1›
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
        have hki : k pub i.val < bn254ScalarModulus := by
          have : beNatOf input < bn254ScalarModulus := by simpa [b_post] using hb
          simpa [k, ← hin] using this
        -- IC_{i+1} decodes to P
        rw [ha1] at hP
        have hPic : ic C vk (i.val + 1) = P := by unfold ic; rw [hP]; rfl
        have hkin : beNatOf input = k pub i.val := by simp [k, hin]
        refine ⟨by omega, fun j hj => ?_, fun h => by omega, fun _ => ?_, by omega⟩
        · rw [hi1] at hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
          · exact hk j hj
          · exact hki
        · rcases Nat.eq_zero_or_pos i.val with h0' | hpos'
          · -- the first step: the running sum is IC₀, read from the key
            have hprep : prep = vk.vk_ic.val[0]! := h0 h0'
            rw [hprep] at hQ
            have hQic : ic C vk 0 = Q := by unfold ic; rw [hQ]; rfl
            refine ⟨fun j hj => ?_, ?_⟩
            · rw [hi1, h0'] at hj
              rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
              · rw [hQ, hQic]
              · rw [h0'] at hP hPic; rw [hP, hPic]
            · rw [hp1, hi1, h0', hkin]
              rw [h0'] at hPic
              simp [vkx, hPic, hQic, add_comm, h0']
          · -- a later step: the running sum is vkx i
            obtain ⟨hdec, hacc⟩ := hpos hpos'
            have hQ' : Q = vkx C vk pub i.val := by rw [hQ] at hacc; exact Option.some.inj hacc
            refine ⟨fun j hj => ?_, ?_⟩
            · rw [hi1] at hj
              rcases Nat.lt_or_ge j (i.val + 1) with hj' | hj'
              · exact hdec j (by omega)
              · have : j = i.val + 1 := by omega
                subst this; rw [hP, hPic]
            · rw [hp1, hi1, hQ', ← hPic, hkin]
              simp only [vkx, Finset.sum_range_succ]
              abel_nf
    · -- the loop is done (i = 7): return the running sum
      rename_i hge
      have hi7 : i.val = 7 := by simp [groth16.NR_PUBLIC_INPUTS] at hge; scalar_tac
      simp only [WP.spec_ok]
      intro p hp
      cases hp
      obtain ⟨hdec, hacc⟩ := hpos (by omega)
      rw [hi7] at hk hdec hacc
      exact ⟨hk, fun j hj => hdec j (by omega), hacc⟩
  · -- before the first step: the running sum is IC₀
    refine ⟨by simp, fun j hj => by simp at hj, fun _ => ?_, fun h => by simp at h⟩
    rw [prepared_public_inputs_post, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
    rfl
/-- Bytes `off .. off + m` of `a`, read one by one. -/
theorem bytesAt_eq_of {n m : Usize} (a : Std.Array U8 n) (off : Nat) (h : off + m.val ≤ n.val)
    (b : Std.Array U8 m) (hb : ∀ t, t < m.val → a.val[off + t]! = b.val[t]!) :
    bytesAt a off m h = b := by
  rw [Std.Array.eq_iff]
  apply List.ext_getElem (by simp [bytesAt]; omega)
  intro t h1 h2
  have ht : t < m.val := by simpa using h2
  have := hb t ht
  simp only [List.getElem!_eq_getElem?_getD] at this
  rw [List.getElem?_eq_getElem (by simp; omega), List.getElem?_eq_getElem (by simpa using h2)] at this
  simpa [bytesAt] using this

/-! ## `verify`: the pairing check -/

theorem verify_spec (pa : Std.Array U8 64#usize) (pb : Std.Array U8 128#usize)
    (pc : Std.Array U8 64#usize) (pub : Std.Array (Std.Array U8 32#usize) 7#usize)
    (vk : groth16.VerifyingKey) :
    groth16.verify (solanaBn254 s) pa pb pc pub vk ⦃ r => r = .Ok true →
      (∀ j, j < 7 → k pub j < bn254ScalarModulus) ∧
      (∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) = some (ic C vk j)) ∧
      ∃ (A Cp α : G1) (B β γ δ : G2),
        C.decodeG1 pa = some A ∧ C.decodeG2 pb = some B ∧ C.decodeG1 pc = some Cp ∧
        C.decodeG1 vk.vk_alpha_g1 = some α ∧ C.decodeG2 vk.vk_beta_g2 = some β ∧
        C.decodeG2 vk.vk_gamme_g2 = some γ ∧ C.decodeG2 vk.vk_delta_g2 = some δ ∧
        C.e A B * C.e (vkx C vk pub 7) γ * C.e Cp δ * C.e α β = 1 ⦄ := by
  unfold groth16.verify
  step with prepare_inputs_spec C pub vk
  split
  · rename_i p
    simp only [solanaBn254]
    step*
    intro _
    -- the pairing answered with last byte 1
    have h31 : r1.val[31]! = 1#u8 := by
      have hi : i = 1#u8 := UScalar.eq_of_val_eq (by simpa using ‹¬(i != 1#u8) = true›)
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
      simpa [i_post] using hi
    obtain ⟨P₁, P₂, P₃, P₄, Q₁, Q₂, Q₃, Q₄, d1, d2, d3, d4, d5, d6, d7, d8, heq⟩ :=
      C.pairing _ _ ‹s.pairing pairing_input8 = some r1› h31
    -- the eight slices of the pairing input are the proof's and the key's points
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
        simp (disch := omega) only [pairing_input8_post, pairing_input7_post, pairing_input6_post, pairing_input5_post, pairing_input4_post, pairing_input3_post, pairing_input2_post, pairing_input1_post, copied, if_pos, Nat.add_sub_cancel_left]
    rw [sA] at d1; rw [sB] at d2; rw [sP] at d3; rw [sG] at d4
    rw [sC] at d5; rw [sD] at d6; rw [sAl] at d7; rw [sBe] at d8
    obtain ⟨hk, hic, hvkx⟩ := r_post p rfl
    rw [hvkx] at d3
    cases d3
    exact ⟨hk, hic, P₁, P₃, P₄, Q₁, Q₄, Q₂, Q₃, d1, d2, d5, d7, d8, d4, d6, heq⟩
  · simp

/-! ## `verify_proof`: what the program's verifier checks -/

/-- `vk_x` for a proof: `IC₀ + Σ kⱼ · ICⱼ₊₁` over its seven public inputs,
    read big-endian, in circuit order. -/
def vkxOf (vk : groth16.VerifyingKey) (proof : transact.Proof) : G1 :=
  ic C vk 0 + ∑ j ∈ Finset.range 7, beNatOf ((publicInputs proof)[j]!) • ic C vk (j + 1)

/-- **The program's Groth16 verifier checks the Groth16 equation.** If
    `verify_proof` accepts a proof (with any verifying key, on syscalls that
    meet their contracts), then its seven public inputs are below r, the
    key's and the proof's points decode, and
    `e(A', B) · e(vk_x, γ) · e(C, δ) · e(α, β) = 1`, where `A'` is the point
    `negate_g1` made from `proof_a`. -/
theorem verify_proof_checks_equation (proof : transact.Proof) (vk : groth16.VerifyingKey)
    (h : groth16.verify_proof (solanaBn254 s) proof vk = ok true) :
    ∃ a', negateG1 proof.proof_a = ok (some a') ∧
      (∀ j, j < 7 → beNatOf ((publicInputs proof)[j]!) < bn254ScalarModulus) ∧
      (∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) = some (ic C vk j)) ∧
      ∃ (A Cp α : G1) (B β γ δ : G2),
        C.decodeG1 a' = some A ∧ C.decodeG2 proof.proof_b = some B ∧
        C.decodeG1 proof.proof_c = some Cp ∧
        C.decodeG1 vk.vk_alpha_g1 = some α ∧ C.decodeG2 vk.vk_beta_g2 = some β ∧
        C.decodeG2 vk.vk_gamme_g2 = some γ ∧ C.decodeG2 vk.vk_delta_g2 = some δ ∧
        C.e A B * C.e (vkxOf C vk proof) γ * C.e Cp δ * C.e α β = 1 := by
  unfold groth16.verify_proof at h
  obtain ⟨n0, hn0, h⟩ := bind_eq_ok' h
  obtain ⟨n1, hn1, h⟩ := bind_eq_ok' h
  obtain ⟨c0, hc0, h⟩ := bind_eq_ok' h
  obtain ⟨c1, hc1, h⟩ := bind_eq_ok' h
  obtain ⟨o, ho, h⟩ := bind_eq_ok' h
  rcases o with _ | a'
  · simp at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok' h
  rcases r with v | e
  · simp only [ok.injEq] at h
    subst h
    -- the public-input array is the proof's public inputs, in circuit order
    have e0 := (WP.spec_equiv_exists _ _).mp (Std.Array.index_usize_spec proof.input_nullifiers 0#usize (by simp))
    have e1 := (WP.spec_equiv_exists _ _).mp (Std.Array.index_usize_spec proof.input_nullifiers 1#usize (by simp))
    have e2 := (WP.spec_equiv_exists _ _).mp (Std.Array.index_usize_spec proof.output_commitments 0#usize (by simp))
    have e3 := (WP.spec_equiv_exists _ _).mp (Std.Array.index_usize_spec proof.output_commitments 1#usize (by simp))
    obtain ⟨_, h0', rfl⟩ := e0; obtain ⟨_, h1', rfl⟩ := e1
    obtain ⟨_, h2', rfl⟩ := e2; obtain ⟨_, h3', rfl⟩ := e3
    rw [h0', ok.injEq] at hn0; rw [h1', ok.injEq] at hn1
    rw [h2', ok.injEq] at hc0; rw [h3', ok.injEq] at hc1
    subst hn0 hn1 hc0 hc1
    obtain ⟨_, hv, hpost⟩ := (WP.spec_equiv_exists _ _).mp (verify_spec C a' proof.proof_b proof.proof_c _ vk)
    rw [hv, ok.injEq] at hr
    subst hr
    obtain ⟨hk, hic, A, Cp, α, B, β, γ, δ, d1, d2, d3, d4, d5, d6, d7, heq⟩ := hpost rfl
    have hpub : ∀ j, k (Std.Array.make 7#usize [proof.root, proof.public_amount, proof.ext_data_hash,
        proof.input_nullifiers.val[0], proof.input_nullifiers.val[1], proof.output_commitments.val[0],
        proof.output_commitments.val[1]] (by simp)) j = beNatOf ((publicInputs proof)[j]!) := by
      intro j; simp [k, publicInputs, Std.Array.make, List.getElem!_eq_getElem?_getD]
    refine ⟨a', ho, fun j hj => ?_, hic, A, Cp, α, B, β, γ, δ, d1, d2, d3, d4, d5, d6, d7, ?_⟩
    · rw [← hpub]; exact hk j hj
    · have : vkxOf C vk proof = vkx C vk (Std.Array.make 7#usize [proof.root, proof.public_amount,
          proof.ext_data_hash, proof.input_nullifiers.val[0], proof.input_nullifiers.val[1],
          proof.output_commitments.val[0], proof.output_commitments.val[1]] (by simp)) 7 := by
        simp only [vkxOf, vkx, hpub]
      rw [this]; exact heq
  · simp at h

/-- **The program's Groth16 check, in full.** If `verify_proof` accepts a
    proof (any key, syscalls meeting their contracts), then the public inputs
    are below r, the points decode, and, with `A` the point in `proof_a` as the
    syscalls read it, `e(-A, B) · e(vk_x, γ) · e(C, δ) · e(α, β) = 1`: the
    Groth16 equation `e(A, B) = e(α, β) · e(vk_x, γ) · e(C, δ)`, rearranged as
    the program checks it. -/
theorem verify_proof_groth16 (proof : transact.Proof) (vk : groth16.VerifyingKey)
    (h : groth16.verify_proof (solanaBn254 s) proof vk = ok true) :
    (∀ j, j < 7 → beNatOf ((publicInputs proof)[j]!) < bn254ScalarModulus) ∧
    (∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) = some (ic C vk j)) ∧
    ∃ (A Cp α : G1) (B β γ δ : G2),
      C.decodeG1 proof.proof_a = some A ∧ C.decodeG2 proof.proof_b = some B ∧
      C.decodeG1 proof.proof_c = some Cp ∧
      C.decodeG1 vk.vk_alpha_g1 = some α ∧ C.decodeG2 vk.vk_beta_g2 = some β ∧
      C.decodeG2 vk.vk_gamme_g2 = some γ ∧ C.decodeG2 vk.vk_delta_g2 = some δ ∧
      C.e (-A) B * C.e (vkxOf C vk proof) γ * C.e Cp δ * C.e α β = 1 := by
  obtain ⟨a', hneg, hk, hic, A', Cp, α, B, β, γ, δ, d1, d2, d3, d4, d5, d6, d7, heq⟩ :=
    verify_proof_checks_equation C proof vk h
  obtain ⟨P, hPa, hPa'⟩ := negateG1_decode hneg
  -- the point negate_g1 produced is minus the point in proof_a
  rw [C.decodeG1_eq, hPa', Option.map_some, C.embed_neg, Option.some.injEq] at d1
  refine ⟨hk, hic, C.embed P, Cp, α, B, β, γ, δ, ?_, d2, d3, d4, d5, d6, d7, ?_⟩
  · rw [C.decodeG1_eq, hPa, Option.map_some]
  · rw [d1]; exact heq

end

/-! ## The program's verifier -/

/-- **The program's verifier** (`Crypto.proofVerifier`: the extracted
    `verify_proof` with the extracted `VERIFYING_KEY`, on the deployment's
    `alt_bn128` syscalls) accepts only proofs that satisfy the Groth16
    equation for the program's key. -/
theorem programVerifier_groth16 {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT]
    (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) (proof : transact.Proof)
    (h : c.proofVerifier.verify proof = ok true) :
    let vk := verifying_key.VERIFYING_KEY
    (∀ j, j < 7 → beNatOf ((publicInputs proof)[j]!) < bn254ScalarModulus) ∧
    (∀ j, j < 8 → C.decodeG1 (vk.vk_ic.val[j]!) = some (ic C vk j)) ∧
    ∃ (A Cp α : G1) (B β γ δ : G2),
      C.decodeG1 proof.proof_a = some A ∧ C.decodeG2 proof.proof_b = some B ∧
      C.decodeG1 proof.proof_c = some Cp ∧
      C.decodeG1 vk.vk_alpha_g1 = some α ∧ C.decodeG2 vk.vk_beta_g2 = some β ∧
      C.decodeG2 vk.vk_gamme_g2 = some γ ∧ C.decodeG2 vk.vk_delta_g2 = some δ ∧
      C.e (-A) B * C.e (vkxOf C vk proof) γ * C.e Cp δ * C.e α β = 1 :=
  verify_proof_groth16 C proof _ h

/-! ## Groth16 soundness, at the equation

`Groth16Sound` (Model/Crypto.lean) assumes "the program's verifier accepts ⇒
the circuit's statement holds", which also trusts the verifier code. With the
theorems above, it follows from the cryptographic assumption alone: Groth16
soundness for the program's key, stated about the equation. -/

/-- **Hypothesis (Groth16 soundness for key `vk`, per execution):** every proof
    in `proofs` whose public inputs are below r and whose points satisfy the
    Groth16 equation for `vk` proves the circuit's statement `stmt` about its
    public inputs. -/
def Groth16EquationSound {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT] {s : AltBn128}
    (C : AltBn128Contracts s G1 G2 GT) (vk : groth16.VerifyingKey)
    (stmt : List (Std.Array U8 32#usize) → Prop) (proofs : Set transact.Proof) : Prop :=
  ∀ p ∈ proofs, ∀ (A Cp α : G1) (B β γ δ : G2),
    (∀ j, j < 7 → beNatOf ((publicInputs p)[j]!) < bn254ScalarModulus) →
    C.decodeG1 p.proof_a = some A → C.decodeG2 p.proof_b = some B →
    C.decodeG1 p.proof_c = some Cp →
    C.decodeG1 vk.vk_alpha_g1 = some α → C.decodeG2 vk.vk_beta_g2 = some β →
    C.decodeG2 vk.vk_gamme_g2 = some γ → C.decodeG2 vk.vk_delta_g2 = some δ →
    C.e (-A) B * C.e (vkxOf C vk p) γ * C.e Cp δ * C.e α β = 1 →
    stmt (publicInputs p)

/-- `Groth16Sound` follows from Groth16 soundness for the program's key: the
    program's verifier code is no longer part of the assumption. -/
theorem groth16Sound_of_equation {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT]
    (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (stmt : List (Std.Array U8 32#usize) → Prop) (proofs : Set transact.Proof)
    (h : Groth16EquationSound C verifying_key.VERIFYING_KEY stmt proofs) :
    Groth16Sound c stmt proofs := by
  intro p hp hv
  obtain ⟨hk, _, A, Cp, α, B, β, γ, δ, d1, d2, d3, d4, d5, d6, d7, heq⟩ :=
    programVerifier_groth16 c C p hv
  exact h p hp A Cp α B β γ δ hk d1 d2 d3 d4 d5 d6 d7 heq

end PrivacyCash.Proofs.Groth16
