import code_model.generated.Funs
import code_model.hand_written.SyscallContracts
open Aeneas Aeneas.Std Result ControlFlow

/-! # `fv_verify_proof_full_entry`: the byte-copy loops

The verifier builds its syscall inputs with 13 loops, each copying a fixed-size byte array into
a larger buffer at an offset. Aeneas turns each one into a `loop` over a generated body.
`copy_loop_spec` proves once what such a loop computes -- the buffer with the source written at
the offset -- and each `loopN_spec` below only checks that its generated body has that shape.

These loops cannot fail, so the lemmas are total: the loop returns `ok`, with this result. -/

namespace zkcash

/-- Reading a list after `set`. -/
theorem getElem!_set' {α} [Inhabited α] (l : List α) (j k : ℕ) (x : α) :
    (l.set j x)[k]! = if j = k ∧ k < l.length then x else l[k]! := by
  by_cases h : j = k <;> by_cases h2 : k < l.length <;> simp_all

/-- A bounds-checked read equals the default-returning one; lets proofs use `l[i]!` throughout. -/
theorem getElem_eq_getElem! {α} [Inhabited α] (l : List α) (i : ℕ) (h : i < l.length) :
    l[i]'h = l[i]! := (getElem!_pos l i h).symm

/-- Every copy loop in the verifier has this shape: while `c < L`, write `src[c]` to
    `dst[off + c]`, then `c := c + 1`. Its result is `dst` with `src` placed at `off`. -/
theorem copy_loop_spec {N : Usize} (L off : ℕ) (src : List Std.U8) (dst : Array Std.U8 N)
    (hL : off + L ≤ N.val)
    (body : Array Std.U8 N × Std.Usize → Result (ControlFlow (Array Std.U8 N × Std.Usize) (Array Std.U8 N)))
    (hbody : ∀ (cur : Array Std.U8 N) (c : Std.Usize), c.val ≤ L → body (cur, c) ⦃ r =>
      match r with
      | .cont (nxt, c') => c.val < L ∧ c'.val = c.val + 1 ∧ nxt.val = cur.val.set (off + c.val) src[c.val]!
      | .done y => L ≤ c.val ∧ y = cur ⦄) :
    loop body (dst, 0#usize) ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if off ≤ i ∧ i < off + L then src[i - off]! else dst.val[i]! ⦄ := by
  apply loop.spec_decr_nat (measure := fun (x : Array Std.U8 N × Std.Usize) => L - x.2.val)
    (inv := fun x => x.2.val ≤ L ∧
      ∀ i : ℕ, x.1.val[i]! = if off ≤ i ∧ i < off + x.2.val then src[i - off]! else dst.val[i]!)
  · rintro ⟨cur, c⟩ ⟨hc, hinv⟩
    simp only at hc hinv
    apply WP.spec_mono (hbody cur c hc)
    rintro (⟨nxt, c'⟩ | y)
    · rintro ⟨hlt, hc', hnxt⟩
      dsimp only
      refine ⟨⟨by omega, fun k => ?_⟩, by omega⟩
      have hlen := cur.property
      rw [hnxt, getElem!_set', hinv]
      by_cases hk : k = off + c.val
      · subst hk; simp only [hlen, true_and]
        rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
      · rw [if_neg (by omega)]
        by_cases h1 : off ≤ k ∧ k < off + c.val
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]
    · rintro ⟨hge, rfl⟩ k
      rw [hinv]
      have : c.val = L := by omega
      rw [this]
  · simp

theorem loop1_spec (proof_a : Array Std.U8 64#usize) (pi : Array Std.U8 768#usize) :
    utils.fv_verify_proof_full_entry_loop1 proof_a pi 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if 0 ≤ i ∧ i < 0 + 64 then proof_a.val[i - 0]! else pi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop1
  apply copy_loop_spec 64 0 proof_a.val pi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop1.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop2_spec (proof_b : Array Std.U8 128#usize) (pi : Array Std.U8 768#usize) (off : Std.Usize)
    (hoff : off.val + 128 ≤ 768) :
    utils.fv_verify_proof_full_entry_loop2 proof_b pi off 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if off.val ≤ i ∧ i < off.val + 128 then proof_b.val[i - off.val]! else pi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop2
  apply copy_loop_spec 128 off.val proof_b.val pi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop2.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop3_spec (prepared_public_inputs : Array Std.U8 64#usize) (pi : Array Std.U8 768#usize) (off : Std.Usize)
    (hoff : off.val + 64 ≤ 768) :
    utils.fv_verify_proof_full_entry_loop3 prepared_public_inputs pi off 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if off.val ≤ i ∧ i < off.val + 64 then prepared_public_inputs.val[i - off.val]! else pi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop3
  apply copy_loop_spec 64 off.val prepared_public_inputs.val pi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop3.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop4_spec (vk_gamme_g2 : Array Std.U8 128#usize) (pi : Array Std.U8 768#usize) (off : Std.Usize)
    (hoff : off.val + 128 ≤ 768) :
    utils.fv_verify_proof_full_entry_loop4 vk_gamme_g2 pi off 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if off.val ≤ i ∧ i < off.val + 128 then vk_gamme_g2.val[i - off.val]! else pi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop4
  apply copy_loop_spec 128 off.val vk_gamme_g2.val pi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop4.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop5_spec (proof_c : Array Std.U8 64#usize) (pi : Array Std.U8 768#usize) (off : Std.Usize)
    (hoff : off.val + 64 ≤ 768) :
    utils.fv_verify_proof_full_entry_loop5 proof_c pi off 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if off.val ≤ i ∧ i < off.val + 64 then proof_c.val[i - off.val]! else pi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop5
  apply copy_loop_spec 64 off.val proof_c.val pi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop5.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop6_spec (vk_delta_g2 : Array Std.U8 128#usize) (pi : Array Std.U8 768#usize) (off : Std.Usize)
    (hoff : off.val + 128 ≤ 768) :
    utils.fv_verify_proof_full_entry_loop6 vk_delta_g2 pi off 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if off.val ≤ i ∧ i < off.val + 128 then vk_delta_g2.val[i - off.val]! else pi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop6
  apply copy_loop_spec 128 off.val vk_delta_g2.val pi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop6.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop7_spec (vk_alpha_g1 : Array Std.U8 64#usize) (pi : Array Std.U8 768#usize) (off : Std.Usize)
    (hoff : off.val + 64 ≤ 768) :
    utils.fv_verify_proof_full_entry_loop7 vk_alpha_g1 pi off 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if off.val ≤ i ∧ i < off.val + 64 then vk_alpha_g1.val[i - off.val]! else pi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop7
  apply copy_loop_spec 64 off.val vk_alpha_g1.val pi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop7.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop8_spec (vk_beta_g2 : Array Std.U8 128#usize) (pi : Array Std.U8 768#usize) (off : Std.Usize)
    (hoff : off.val + 128 ≤ 768) :
    utils.fv_verify_proof_full_entry_loop8 vk_beta_g2 pi off 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if off.val ≤ i ∧ i < off.val + 128 then vk_beta_g2.val[i - off.val]! else pi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop8
  apply copy_loop_spec 128 off.val vk_beta_g2.val pi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop8.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop0_loop0_spec (vk_ic : Array (Array Std.U8 64#usize) 8#usize) (idx : Std.Usize)
    (hidx : idx.val < 7) (mi : Array Std.U8 96#usize) :
    utils.fv_verify_proof_full_entry_loop0_loop0 vk_ic idx mi 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if 0 ≤ i ∧ i < 0 + 64 then (vk_ic.val[idx.val + 1]!).val[i - 0]! else mi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop0_loop0
  apply copy_loop_spec 64 0 (vk_ic.val[idx.val + 1]!).val mi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop0_loop0.body]
  split
  · step*
    have := a.property
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a1_post, Array.set_val_eq, i1_post, a_post, getElem_eq_getElem!, i_post, Nat.zero_add]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop0_loop1_spec (pubs : Array (Array Std.U8 32#usize) 7#usize) (idx : Std.Usize)
    (hidx : idx.val < 7) (mi : Array Std.U8 96#usize) :
    utils.fv_verify_proof_full_entry_loop0_loop1 pubs idx mi 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if 64 ≤ i ∧ i < 64 + 32 then (pubs.val[idx.val]!).val[i - 64]! else mi.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop0_loop1
  apply copy_loop_spec 32 64 (pubs.val[idx.val]!).val mi (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop0_loop1.body]
  split
  · step*
    have := a.property
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a1_post, Array.set_val_eq, i1_post, a_post, getElem_eq_getElem!, i_post]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop0_loop2_spec (mul_res : Array Std.U8 64#usize) (ai : Array Std.U8 128#usize) :
    utils.fv_verify_proof_full_entry_loop0_loop2 mul_res ai 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if 0 ≤ i ∧ i < 0 + 64 then mul_res.val[i - 0]! else ai.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop0_loop2
  apply copy_loop_spec 64 0 mul_res.val ai (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop0_loop2.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i_post, getElem_eq_getElem!, Nat.zero_add]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩

theorem loop0_loop3_spec (prep : Array Std.U8 64#usize) (ai : Array Std.U8 128#usize) :
    utils.fv_verify_proof_full_entry_loop0_loop3 prep ai 0#usize ⦃ r =>
      ∀ i : ℕ, r.val[i]! = if 64 ≤ i ∧ i < 64 + 64 then prep.val[i - 64]! else ai.val[i]! ⦄ := by
  unfold utils.fv_verify_proof_full_entry_loop0_loop3
  apply copy_loop_spec 64 64 prep.val ai (by scalar_tac)
  intro cur c hc
  simp only [utils.fv_verify_proof_full_entry_loop0_loop3.body]
  split
  · step*
    refine ⟨by scalar_tac, by scalar_tac, ?_⟩
    simp only [a_post, Array.set_val_eq, i1_post, i_post, getElem_eq_getElem!]
  · simp only [WP.spec_ok]; exact ⟨by scalar_tac, trivial⟩
