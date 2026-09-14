import proofs.VerifyProof.CopyLoops
open Aeneas Aeneas.Std Result ControlFlow

/-! # `fv_verify_proof_full_entry`: the public-input accumulation loop

`vk_x = IC₀ + Σ kᵢ · ICᵢ₊₁` is computed by a loop that calls the multiplication and addition
syscalls, which may fail. So, unlike the copy loops, the result here is conditional: IF the loop
reports success, THEN every scalar was range-checked, every IC entry decodes, and the result
decodes to that sum (`loop0_sound`, by induction on the iterations left). The meaning of the
syscall answers comes only from `curve_shim.AltBn128Syscalls`. -/

namespace zkcash

/-- A `do` step succeeded iff its first action succeeded and so did the rest. -/
theorem bind_eq_ok {α β : Type} (m : Result α) (f : α → Result β) (v : β) :
    (do let x ← m; f x) = ok v ↔ ∃ x, m = ok x ∧ f x = ok v := by
  cases m <;> simp

/-- Use a `⦃ ⦄` spec in the "given it returned `ok x`" direction. -/
theorem post_of_ok {α : Type} {m : Result α} {P : α → Prop} {x : α} (hs : m ⦃ P ⦄) (h : m = ok x) : P x := by
  obtain ⟨y, hy, hp⟩ := WP.spec_imp_exists hs
  rw [h] at hy; cases hy; exact hp

/-- A `Usize` addition that returned `ok x` computed the true sum. -/
theorem add_ok_val {a b x : Std.Usize} (hab : a.val + b.val < 2 ^ 32) (h : a + b = ok x) :
    x.val = a.val + b.val := by
  have hs := UScalar.add_spec (x := a) (y := b) (by scalar_tac)
  exact post_of_ok (x := x) hs h

/-- Run one iteration of the accumulation loop, keeping its body folded. -/
theorem loop0_unfold (vk_ic : Array (Array Std.U8 64#usize) 8#usize)
    (pubs : Array (Array Std.U8 32#usize) 7#usize) (prep : Array Std.U8 64#usize) (ok1 : Bool)
    (idx : Std.Usize) :
    utils.fv_verify_proof_full_entry_loop0 vk_ic pubs prep ok1 idx =
      (do
        let r ← utils.fv_verify_proof_full_entry_loop0.body vk_ic pubs prep ok1 idx
        match r with
        | cont (p, o, i) => utils.fv_verify_proof_full_entry_loop0 vk_ic pubs p o i
        | done r => ok r) := by
  conv => lhs; unfold utils.fv_verify_proof_full_entry_loop0; rw [loop]
  dsimp only
  rcases hb : utils.fv_verify_proof_full_entry_loop0.body vk_ic pubs prep ok1 idx with
    (⟨p, o, i⟩ | r) | e | _ <;> simp only [bind_tc_ok] <;> rfl

variable {G1 G2 GT : Type} [AddCommMonoid G1] [CommMonoid GT] [S : curve_shim.AltBn128Syscalls G1 G2 GT]

/-- The bytes at `off..off+m` of `a` are exactly `src`, given pointwise agreement. -/
theorem bytesAt_eq {n m : Std.Usize} (a : Array Std.U8 n) (off : ℕ) (h : off + m.val ≤ n.val)
    (src : Array Std.U8 m) (hpt : ∀ i, i < m.val → a.val[off + i]! = src.val[i]!) :
    curve_shim.bytesAt a off m h = src := by
  have ha := a.property
  have hs := src.property
  apply Subtype.ext
  apply List.ext_getElem
  · simp only [curve_shim.bytesAt, List.length_take, List.length_drop, ha, hs]; omega
  · intro i h1 h2
    simp only [curve_shim.bytesAt, List.getElem_take, List.getElem_drop]
    rw [getElem_eq_getElem!, getElem_eq_getElem!]
    exact hpt i (by omega)

/-- The G1 point the verifying key's `j`-th IC entry decodes to (0 if it does not decode;
    every theorem below also proves it does decode). -/
def ic (S : curve_shim.AltBn128Syscalls G1 G2 GT) (vk_ic : Array (Array Std.U8 64#usize) 8#usize) (j : ℕ) : G1 :=
  (S.decodeG1 vk_ic.val[j]!).getD 0

/-- One iteration of the accumulation loop, while `ok` is still true: it always continues
    to `idx + 1`, and if `ok` stays true, it has range-checked input `idx` and added
    `k_idx · IC_(idx+1)` to the running point. -/
theorem loop0_body_spec (vk_ic : Array (Array Std.U8 64#usize) 8#usize)
    (pubs : Array (Array Std.U8 32#usize) 7#usize)
    (prep : Array Std.U8 64#usize) (idx : Std.Usize) (hidx : idx.val < 7) r
    (h : utils.fv_verify_proof_full_entry_loop0.body vk_ic pubs prep true idx = ok r) :
    ∃ p o i, r = cont (p, o, i) ∧ i.val = idx.val + 1 ∧
    (o = true →
      curve_shim.natOfBE (pubs.val[idx.val]!) < bn254_r ∧
      S.decodeG1 (vk_ic.val[idx.val + 1]!) = some (ic S vk_ic (idx.val + 1)) ∧
      ∃ acc, S.decodeG1 prep = some acc ∧
        S.decodeG1 p = some (curve_shim.natOfBE (pubs.val[idx.val]!) • ic S vk_ic (idx.val + 1) + acc)) := by
  have hlt : idx < 7#usize := by scalar_tac
  simp only [utils.fv_verify_proof_full_entry_loop0.body, hlt, if_true, curve_shim.fr_lt_modulus_be,
    bind_eq_ok] at h
  obtain ⟨a, ha, b, hb, h⟩ := h
  have ha' := post_of_ok (Array.index_usize_spec pubs idx (by scalar_tac)) ha
  cases hb
  by_cases hk : curve_shim.natOfBE a < bn254_r
  swap
  · -- scalar out of range: ok becomes false
    simp only [curve_shim.natOfBE] at hk
    simp only [hk, decide_false, Bool.false_eq_true, if_false, bind_eq_ok] at h
    obtain ⟨x, hx, h⟩ := h
    simp only [ok.injEq] at h; subst h
    exact ⟨_, _, _, rfl, add_ok_val (by scalar_tac) hx, by simp⟩
  · have hk' := hk
    simp only [curve_shim.natOfBE] at hk'
    simp only [hk', decide_true, if_true, bind_eq_ok] at h
    obtain ⟨mi1, hmi1, mi2, hmi2, om, hom, h⟩ := h
    have hp1 := post_of_ok (loop0_loop0_spec vk_ic idx hidx _) hmi1
    have hp2 := post_of_ok (loop0_loop1_spec pubs idx hidx _) hmi2
    rcases om with _ | mul_res
    · simp only [bind_eq_ok] at h
      obtain ⟨x, hx, h⟩ := h
      simp only [ok.injEq] at h; subst h
      exact ⟨_, _, _, rfl, add_ok_val (by scalar_tac) hx, by simp⟩
    · simp only [bind_eq_ok] at h
      obtain ⟨ai1, hai1, ai2, hai2, oa, hoa, h⟩ := h
      have hq1 := post_of_ok (loop0_loop2_spec mul_res _) hai1
      have hq2 := post_of_ok (loop0_loop3_spec prep _) hai2
      rcases oa with _ | sum
      · obtain ⟨y, hy, h⟩ := h
        simp only [ok.injEq] at hy; subst hy
        obtain ⟨x, hx, h⟩ := (bind_eq_ok (idx + 1#usize) (fun idx1 => ok (cont (prep, false, idx1))) _).mp h
        simp only [ok.injEq] at h; subst h
        exact ⟨_, _, _, rfl, add_ok_val (by scalar_tac) hx, by simp⟩
      · obtain ⟨y, hy, h⟩ := h
        simp only [ok.injEq] at hy; subst hy
        obtain ⟨x, hx, h⟩ := (bind_eq_ok (idx + 1#usize) (fun idx1 => ok (cont (sum, true, idx1))) _).mp h
        simp only [ok.injEq] at h; subst h
        refine ⟨_, _, _, rfl, add_ok_val (by scalar_tac) hx, fun _ => ?_⟩
        -- the four byte ranges the syscalls read are exactly the inputs that were copied in
        have e1 : curve_shim.bytesAt mi2 0 64#usize (by scalar_tac) = vk_ic.val[idx.val + 1]! := by
          apply bytesAt_eq; intro j hj
          have hj : j < 64 := by simpa using hj
          rw [hp2, if_neg (by omega), hp1, if_pos (by omega)]; simp
        have e2 : curve_shim.bytesAt mi2 64 32#usize (by scalar_tac) = pubs.val[idx.val]! := by
          apply bytesAt_eq; intro j hj
          have hj : j < 32 := by simpa using hj
          rw [hp2, if_pos (by omega)]; simp
        have e3 : curve_shim.bytesAt ai2 0 64#usize (by scalar_tac) = mul_res := by
          apply bytesAt_eq; intro j hj
          have hj : j < 64 := by simpa using hj
          rw [hq2, if_neg (by omega), hq1, if_pos (by omega)]; simp
        have e4 : curve_shim.bytesAt ai2 64 64#usize (by scalar_tac) = prep := by
          apply bytesAt_eq; intro j hj
          have hj : j < 64 := by simpa using hj
          rw [hq2, if_pos (by omega)]; simp
        obtain ⟨P, hP, hmul⟩ := S.mul_spec mi2 mul_res hom
        obtain ⟨P', Q, hP', hQ, hsum⟩ := S.add_spec ai2 sum hoa
        rw [e1] at hP
        rw [e2] at hmul
        rw [e3, hmul, Option.some.injEq] at hP'
        rw [e4] at hQ
        have hic : ic S vk_ic (idx.val + 1) = P := by simp only [ic, hP, Option.getD_some]
        rw [getElem_eq_getElem!] at ha'
        rw [ha'] at hk
        refine ⟨hk, by rw [hP, hic], Q, hQ, ?_⟩
        rw [hsum, ← hP', hic]

/-- Once `ok` is false the loop stops at the next check and reports false. -/
theorem loop0_false (vk_ic : Array (Array Std.U8 64#usize) 8#usize)
    (pubs : Array (Array Std.U8 32#usize) 7#usize) (prep : Array Std.U8 64#usize) (idx : Std.Usize) :
    utils.fv_verify_proof_full_entry_loop0 vk_ic pubs prep false idx = ok (prep, false) := by
  rw [loop0_unfold]
  simp only [utils.fv_verify_proof_full_entry_loop0.body]
  split <;> simp

/-- At `idx = 7` the loop is over and returns its state unchanged. -/
theorem loop0_end (vk_ic : Array (Array Std.U8 64#usize) 8#usize)
    (pubs : Array (Array Std.U8 32#usize) 7#usize) (prep : Array Std.U8 64#usize) (ok1 : Bool)
    (idx : Std.Usize) (hidx : 7 ≤ idx.val) :
    utils.fv_verify_proof_full_entry_loop0 vk_ic pubs prep ok1 idx = ok (prep, ok1) := by
  rw [loop0_unfold]
  have : ¬ idx < 7#usize := by scalar_tac
  simp only [utils.fv_verify_proof_full_entry_loop0.body, this, if_false]
  simp

/-- The accumulation loop, from iteration `idx` on: if it reports true, every remaining public
    input was below r, every remaining IC entry decodes, and the result decodes to the starting
    point plus `Σ_{j ∈ [idx, 7)} k_j · IC_(j+1)`. -/
theorem loop0_sound (vk_ic : Array (Array Std.U8 64#usize) 8#usize)
    (pubs : Array (Array Std.U8 32#usize) 7#usize) :
    ∀ (n : ℕ) (idx : Std.Usize) (prep prep' : Array Std.U8 64#usize), 7 - idx.val = n → idx.val < 7 →
    utils.fv_verify_proof_full_entry_loop0 vk_ic pubs prep true idx = ok (prep', true) →
    (∀ j, idx.val ≤ j → j < 7 →
      curve_shim.natOfBE (pubs.val[j]!) < bn254_r ∧ S.decodeG1 (vk_ic.val[j + 1]!) = some (ic S vk_ic (j + 1))) ∧
    ∃ acc, S.decodeG1 prep = some acc ∧
      S.decodeG1 prep' = some (acc + ∑ j ∈ Finset.Ico idx.val 7,
        curve_shim.natOfBE (pubs.val[j]!) • ic S vk_ic (j + 1)) := by
  intro n
  induction n with
  | zero => intro idx _ _ hn hidx; omega
  | succ n ih =>
    intro idx prep prep' hn hidx h
    rw [loop0_unfold] at h
    obtain ⟨r, hr, h⟩ := (bind_eq_ok _ _ _).mp h
    obtain ⟨p, o, i, rfl, hi, hstep⟩ := loop0_body_spec (S := S) vk_ic pubs prep idx hidx r hr
    change utils.fv_verify_proof_full_entry_loop0 vk_ic pubs p o i = ok (prep', true) at h
    cases o with
    | false => rw [loop0_false] at h; simp at h
    | true =>
      obtain ⟨hk, hic, acc, hacc, hp⟩ := hstep rfl
      have hsplit := Finset.sum_eq_sum_Ico_succ_bot (show idx.val < 7 from hidx)
        (fun j => curve_shim.natOfBE (pubs.val[j]!) • ic S vk_ic (j + 1))
      by_cases hi7 : i.val < 7
      · obtain ⟨hall, acc', hacc', hp'⟩ := ih i p prep' (by omega) hi7 h
        rw [hp, Option.some.injEq] at hacc'
        refine ⟨fun j hj1 hj2 => ?_, acc, hacc, ?_⟩
        · by_cases hj : j = idx.val
          · subst hj; exact ⟨hk, hic⟩
          · exact hall j (by omega) hj2
        · rw [hp', ← hacc', hsplit, hi]; abel_nf
      · rw [loop0_end vk_ic pubs p true i (by omega)] at h
        simp only [ok.injEq, Prod.mk.injEq, and_true] at h
        subst h
        have h6 : idx.val = 6 := by omega
        refine ⟨fun j hj1 hj2 => ?_, acc, hacc, ?_⟩
        · have : j = idx.val := by omega
          subst this; exact ⟨hk, hic⟩
        · rw [hp, h6]; simp [add_comm]
