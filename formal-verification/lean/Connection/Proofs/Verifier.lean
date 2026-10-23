import Connection.Proofs.Tree
import PrivacyCash.Proofs.Groth16
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: what the program's verifier guarantees without any syscall assumption

NOT FOR REVIEW: the statements are restated in `Connection/ConnectionTheorems.lean`. -/

namespace Connection
open zkcash_core

private theorem okOf' {α : Type} {m : Result α} {P : α → Prop} (h : m ⦃ P ⦄) : ∃ x, m = ok x ∧ P x :=
  (WP.spec_equiv_exists _ _).mp h

private theorem canonical_of_lt (b : Std.Array U8 32#usize)
    (h : PrivacyCash.Model.beNatOf b < bn254ScalarModulus) : Canonical b := h

/-- If `prepare_inputs`' loop, started at 0, returns `Ok`, every input is canonical. -/
private theorem prepareLoop_canonical {Cb : Type} (B : groth16.Bn254 Cb)
    (pub : Std.Array (Std.Array U8 32#usize) 7#usize) (ic : Std.Array (Std.Array U8 64#usize) 8#usize)
    (acc : Std.Array U8 64#usize) (p : Std.Array U8 64#usize)
    (h : groth16.prepare_inputs_loop B pub ic acc 0#usize = ok (.Ok p)) :
    ∀ j, j < 7 → Canonical (pub.val[j]!) := by
  unfold groth16.prepare_inputs_loop at h
  refine loop_ok_induction _ (fun x : Std.Array U8 64#usize × Usize => 7 - x.2.val)
    (fun x => x.2.val ≤ 7 ∧ ∀ j, j < x.2.val → Canonical (pub.val[j]!))
    (fun r => r = .Ok p → ∀ j, j < 7 → Canonical (pub.val[j]!)) ?_ _ _ ⟨by simp, by simp⟩ h rfl
  rintro ⟨acc, i⟩ r ⟨hi, hinv⟩ hr
  simp only at hi hinv
  have hr : groth16.prepare_inputs_loop.body B pub ic acc i = ok r := hr
  unfold groth16.prepare_inputs_loop.body at hr
  by_cases hlt : i < groth16.NR_PUBLIC_INPUTS
  · rw [if_pos hlt] at hr
    have hlt' : i.val < 7 := by
      have : i.val < groth16.NR_PUBLIC_INPUTS.val := hlt
      simpa [groth16.NR_PUBLIC_INPUTS] using this
    obtain ⟨input, hin, hr⟩ := bindOk hr
    obtain ⟨input', hin', hinv'⟩ := okOf' (Std.Array.index_usize_spec pub i (by simp; omega))
    rw [hin'] at hin; obtain rfl := Result.ok_injective hin
    obtain ⟨b, hb, hr⟩ := bindOk hr
    obtain ⟨b', hb', hbv⟩ := okOf' (PrivacyCash.Proofs.Groth16.is_less_than_bn254_field_size_be_spec input')
    rw [hb'] at hb; obtain rfl := Result.ok_injective hb
    by_cases hbt : decide (beNatOf input' < bn254ScalarModulus) = true
    · rw [hbv, if_pos hbt] at hr
      have hcan : Canonical (pub.val[i.val]!) := by
        rw [getElem!_pos _ _ (by simp; omega), ← hinv']
        exact canonical_of_lt _ (of_decide_eq_true hbt)
      obtain ⟨i1, hi1, hr⟩ := bindOk hr
      obtain ⟨i1', hi1', hi1v⟩ := okOf' (UScalar.add_spec (x := i) (y := 1#usize) (by scalar_tac))
      rw [hi1'] at hi1; obtain rfl := Result.ok_injective hi1
      obtain ⟨a1, -, hr⟩ := bindOk hr
      obtain ⟨o, -, hr⟩ := bindOk hr
      cases o with
      | none =>
        have := Result.ok_injective hr; subst this
        intro hc; cases hc
      | some q =>
        obtain ⟨o1, -, hr⟩ := bindOk hr
        cases o1 with
        | none =>
          have := Result.ok_injective hr; subst this
          intro hc; cases hc
        | some q1 =>
          have := Result.ok_injective hr; subst this
          have hiv : i1'.val = i.val + 1 := by simpa using hi1v
          refine ⟨⟨by show i1'.val ≤ 7; omega, fun j hj => ?_⟩, by show 7 - i1'.val < 7 - i.val; omega⟩
          have hj' : j < i.val + 1 := by rw [← hiv]; exact hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj' with hj'' | rfl
          · exact hinv j hj''
          · exact hcan
    · rw [hbv, if_neg hbt] at hr
      have := Result.ok_injective hr; subst this
      intro hc; cases hc
  · rw [if_neg hlt] at hr
    have := Result.ok_injective hr; subst this
    intro _ j hj
    have : 7 ≤ i.val := by
      have : ¬ i.val < groth16.NR_PUBLIC_INPUTS.val := hlt
      simp [groth16.NR_PUBLIC_INPUTS] at this; omega
    exact hinv j (by omega)

/-- **If the program's verifier accepts a proof, all 7 public inputs are canonical** (below
    the field modulus), whatever the syscalls return. -/
theorem verifyProof_canonical {Cb : Type} (B : groth16.Bn254 Cb) (proof : transact.Proof)
    (vk : groth16.VerifyingKey) (h : groth16.verify_proof B proof vk = ok true) :
    ∀ j, j < 7 → Canonical ((publicInputs proof)[j]!) := by
  unfold groth16.verify_proof at h
  obtain ⟨a, ha, h⟩ := bindOk h
  obtain ⟨a1, ha1, h⟩ := bindOk h
  obtain ⟨a2, ha2, h⟩ := bindOk h
  obtain ⟨a3, ha3, h⟩ := bindOk h
  have e : ∀ (x : Std.Array (Std.Array U8 32#usize) 2#usize) (k : Usize) (v), k.val < 2 →
      x.index_usize k = ok v → v = x.val[k.val]! := by
    intro x k v hk hv
    obtain ⟨v', hv', hvv⟩ := okOf' (Std.Array.index_usize_spec x k (by simp; omega))
    rw [hv'] at hv; obtain rfl := Result.ok_injective hv
    rw [hvv, getElem!_pos _ _ (by simp; omega)]
  have ea := e _ _ _ (by simp) ha; have ea1 := e _ _ _ (by simp) ha1
  have ea2 := e _ _ _ (by simp) ha2; have ea3 := e _ _ _ (by simp) ha3
  obtain ⟨o, -, h⟩ := bindOk h
  cases o with
  | none => have := Result.ok_injective h; cases this
  | some q =>
  obtain ⟨r, hr, h⟩ := bindOk h
  cases r with
  | Err _ => have := Result.ok_injective h; cases this
  | Ok v =>
  unfold groth16.verify at hr
  obtain ⟨r0, hr0, hr⟩ := bindOk hr
  cases r0 with
  | Err _ => have := Result.ok_injective hr; cases this
  | Ok pp =>
  unfold groth16.prepare_inputs at hr0
  obtain ⟨acc, -, hr0⟩ := bindOk hr0
  have hall := prepareLoop_canonical B _ _ acc pp hr0
  intro j hj
  have := hall j hj
  simp only [publicInputs, ea, ea1, ea2, ea3] at this ⊢
  simpa using this

end Connection
