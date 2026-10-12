/-
Facts about the concrete G1 encodings (Model/Bn254.lean): the extracted
`change_endianness` reverses each 32-byte half, and decoding what
`negate_g1` returns gives the negation of the point it was given.
-/
import PrivacyCash.Model.Bn254
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Proofs.G1
open zkcash_core PrivacyCash.Model

/-- A successful `do let x ← m; f x` went through a successful `m`. -/
theorem bind_eq_ok' {α β : Type} {m : Result α} {f : α → Result β} {v : β}
    (h : (do let x ← m; f x) = ok v) : ∃ x, m = ok x ∧ f x = ok v := by
  cases m with
  | ret a => exact ⟨a, rfl, by simpa using h⟩
  | vis e k => simp at h
  | div => simp at h

/-- The inner loop appends `bytes[start .. i]`, last byte first. -/
@[step]
theorem change_endianness_inner_spec (bytes : Slice U8) (vec : alloc.vec.Vec U8)
    (start i : Usize) (hs : start.val ≤ i.val) (hi : i.val ≤ bytes.val.length)
    (hcap : vec.val.length + (i.val - start.val) ≤ Usize.max) :
    utils.change_endianness_loop0_loop0 bytes vec start i ⦃ v =>
      v.val = vec.val ++ ((bytes.val.take i.val).drop start.val).reverse ⦄ := by
  unfold utils.change_endianness_loop0_loop0
  apply loop.spec_decr_nat (fun (x : alloc.vec.Vec U8 × Usize) => x.2.val)
    (fun x => start.val ≤ x.2.val ∧ x.2.val ≤ i.val ∧
      x.1.val = vec.val ++ ((bytes.val.take i.val).drop x.2.val).reverse)
  · rintro ⟨v, j⟩ ⟨hj1, hj2, hv⟩
    dsimp only at hj1 hj2 hv ⊢
    unfold utils.change_endianness_loop0_loop0.body
    split
    · rename_i hgt
      have hjs : start.val < j.val := by scalar_tac
      step*
      · rw [hv]; simp; omega
      · refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        have hl : i1.val < (bytes.val.take i.val).length := by simp; scalar_tac
        have hj : i1.val + 1 = j.val := by scalar_tac
        rw [vec1_post, hv, i2_post, List.drop_eq_getElem_cons hl, hj]
        simp [List.getElem_take]
    · rename_i hle
      simp only [WP.spec_ok]
      have : j.val = start.val := by scalar_tac
      rw [hv, this]
  · exact ⟨hs, le_refl _, by simp⟩

/-- On 64 bytes, `change_endianness` reverses each 32-byte half. -/
theorem change_endianness_64 (a : Std.Array U8 64#usize) :
    utils.change_endianness (Std.Array.to_slice a) ⦃ v => v.val = reverseHalves a.val ⦄ := by
  unfold utils.change_endianness utils.change_endianness_loop0
  apply loop.spec_decr_nat (fun (x : alloc.vec.Vec U8 × Usize) => 64 - x.2.val)
    (fun x => (x.2.val = 0 ∨ x.2.val = 32 ∨ x.2.val = 64) ∧
      x.1.val = (a.val.take (min x.2.val 32)).reverse ++ ((a.val.drop 32).take (x.2.val - 32)).reverse)
  · rintro ⟨v, st⟩ ⟨hst, hv⟩
    dsimp only at hst hv ⊢
    unfold utils.change_endianness_loop0.body
    have hlen : (Std.Array.to_slice a).val.length = 64 := by simp
    have hlen' : (Std.Array.to_slice a).len.val = 64 := by simp
    dsimp only
    split
    · rename_i hlt
      have hst' : st.val = 0 ∨ st.val = 32 := by scalar_tac
      step*
      have hge : ¬ i2 < 32#usize := by scalar_tac
      simp only [hge, if_false]
      step*
      · rw [hv]; simp; scalar_tac
      · have hsl : (Std.Array.to_slice a).val = a.val := by simp [Std.Array.to_slice]
        have hl : a.val.length = 64 := by simp
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [vec1_post, hv, hsl]
        rcases hst' with h | h
        · have h3 : i3.val = 32 := by scalar_tac
          simp [h, h3]
        · have h3 : i3.val = 64 := by scalar_tac
          simp [h, h3, List.take_of_length_le, hl]
    · rename_i hge
      simp only [WP.spec_ok]
      have h : st.val = 64 := by scalar_tac
      have hl : a.val.length = 64 := by simp
      rw [hv, h]
      simp [reverseHalves, List.take_of_length_le, hl]
  · exact ⟨Or.inl rfl, by simp⟩

/-! ## Little-endian bytes -/

theorem leNat_foldr (l : List U8) (acc : Nat) :
    l.foldr (fun b acc => b.val + 256 * acc) acc = leNatOfList l + 256 ^ l.length * acc := by
  induction l with
  | nil => simp [leNatOfList]
  | cons x t ih =>
    simp only [List.foldr_cons, List.length_cons]
    rw [ih]
    simp only [leNatOfList, List.foldr_cons]
    ring

theorem leNat_append_single (l : List U8) (b : U8) :
    leNatOfList (l ++ [b]) = leNatOfList l + 256 ^ l.length * b.val := by
  rw [leNatOfList, List.foldr_append]
  simp only [List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
  rw [leNat_foldr]

/-- Byte `i` of `n`, little-endian. -/
def byteAt (n i : Nat) : U8 := U8.ofNatCore (n / 256 ^ i % 256) (by
  have : n / 256 ^ i % 256 < 256 := Nat.mod_lt _ (by norm_num)
  simp only [UScalarTy.numBits]; omega)

theorem byteAt_val (n i : Nat) : (byteAt n i).val = n / 256 ^ i % 256 := by
  simp [byteAt]

theorem leBytes32_eq (n : Nat) : leBytes32 n = (List.range 32).map (byteAt n) := rfl

/-- The first `k` little-endian bytes of `n` read back as `n mod 256^k`. -/
theorem leNat_range (n k : Nat) : leNatOfList ((List.range k).map (byteAt n)) = n % 256 ^ k := by
  induction k with
  | zero => simp [leNatOfList, Nat.mod_one]
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, leNat_append_single, ih, byteAt_val]
    simp only [List.length_map, List.length_range]
    rw [Nat.mod_pow_succ]

theorem leNat_leBytes32 (n : Nat) (h : n < 256 ^ 32) : leNatOfList (leBytes32 n) = n := by
  rw [leBytes32_eq, leNat_range, Nat.mod_eq_of_lt h]

/-! ## Encoding then decoding a point gives it back -/

instance : NeZero bn254BaseModulus := ⟨by decide⟩

theorem q_lt : bn254BaseModulus < 2 ^ 254 := by decide

theorem leBytes32_length (n : Nat) : (leBytes32 n).length = 32 := by simp [leBytes32]

theorem leBytes32_take31 (n : Nat) : (leBytes32 n).take 31 = (List.range 31).map (byteAt n) := by
  rw [leBytes32_eq, ← List.map_take, List.take_range]; rfl

theorem leBytes32_getD31 (n : Nat) : ((leBytes32 n).getD 31 0#u8).val = n / 256 ^ 31 % 256 := by
  rw [leBytes32_eq, List.getD_eq_getElem _ _ (by simp)]
  simp [byteAt_val]

/-- A valid point that is not the identity decodes from its own encoding. -/
theorem deserialize_toBytes (Q : G1Affine) (hinf : Q.infinity = false)
    (hcurve : Q.y ^ 2 = Q.x ^ 3 + 3) : deserializeUncompressed Q.toBytes = some Q := by
  have hx := ZMod.val_lt Q.x
  have hy := ZMod.val_lt Q.y
  have hq := q_lt
  have hlx := leBytes32_length Q.x.val
  -- the bytes: x then y, each 32 bytes little-endian
  have htake : (Q.toBytes.val).take 32 = leBytes32 Q.x.val := by
    simp [G1Affine.toBytes, hlx]
  have hdrop : ((Q.toBytes.val).drop 32).take 31 = (List.range 31).map (byteAt Q.y.val) := by
    simp [G1Affine.toBytes, hlx, leBytes32_take31]
  have htop : ((Q.toBytes.val).getD 63 0#u8).val = Q.y.val / 256 ^ 31 := by
    have : (Q.toBytes.val).getD 63 0#u8 = (leBytes32 Q.y.val).getD 31 0#u8 := by
      simp only [G1Affine.toBytes, Std.Array.from_val, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by simp [hlx])]
      simp [hlx]
    rw [this, leBytes32_getD31]
    apply Nat.mod_eq_of_lt
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc Q.y.val < 2 ^ 254 := lt_trans hy hq
      _ ≤ 256 * 256 ^ 31 := by norm_num
  have hxn : leNatOfList ((Q.toBytes.val).take 32) = Q.x.val := by
    rw [htake, leNat_leBytes32 _ (lt_trans hx (lt_trans hq (by norm_num)))]
  have hyn : leNatOfList (((Q.toBytes.val).drop 32).take 31) +
      (((Q.toBytes.val).getD 63 0#u8).val % 64) * 256 ^ 31 = Q.y.val := by
    have hsmall : Q.y.val / 256 ^ 31 < 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc Q.y.val < 2 ^ 254 := lt_trans hy hq
        _ = 64 * 256 ^ 31 := by norm_num
    rw [hdrop, leNat_range, htop, Nat.mod_eq_of_lt hsmall]
    exact Nat.mod_add_div' _ _
  have hflag64 : ((Q.toBytes.val).getD 63 0#u8).val / 64 % 2 = 0 := by
    rw [htop]
    have : Q.y.val / 256 ^ 31 < 64 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc Q.y.val < 2 ^ 254 := lt_trans hy hq
        _ = 64 * 256 ^ 31 := by norm_num
    rw [Nat.div_eq_of_lt this]
  have hflag128 : ((Q.toBytes.val).getD 63 0#u8).val / 128 % 2 = 0 := by
    rw [htop]
    have : Q.y.val / 256 ^ 31 < 128 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]
      calc Q.y.val < 2 ^ 254 := lt_trans hy hq
        _ ≤ 128 * 256 ^ 31 := by norm_num
    rw [Nat.div_eq_of_lt this]
  unfold deserializeUncompressed
  simp only [hflag64, hflag128, hxn, hyn]
  simp only [show ((0 : Nat) == 1) = false from rfl, Bool.and_false, Bool.false_eq_true, if_false,
    not_le.mpr hx, not_le.mpr hy, ZMod.natCast_zmod_val, hcurve, if_true]
  cases Q
  simp_all

/-! ## Small facts -/

theorem reverseHalves_involutive (l : List U8) (h : l.length = 64) :
    reverseHalves (reverseHalves l) = l := by
  simp only [reverseHalves]
  have h1 : ((l.take 32).reverse).length = 32 := by simp; omega
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega)]
  simp

/-- What arkworks decodes is the identity or a point on the curve. -/
theorem deserialize_some {b : Std.Array U8 64#usize} {P : G1Affine}
    (h : deserializeUncompressed b = some P) :
    P = ⟨0, 0, true⟩ ∨ (P.infinity = false ∧ P.y ^ 2 = P.x ^ 3 + 3) := by
  unfold deserializeUncompressed at h
  simp only at h
  split_ifs at h with h1 h2 h3 h4 h5
  · exact Or.inl (Option.some.inj h).symm
  · cases h; exact Or.inr ⟨rfl, h5⟩

theorem three_ne_zero : (3 : ZMod bn254BaseModulus) ≠ 0 := by decide

/-- All-zero bytes do not decode: (0, 0) is not on the curve. -/
theorem deserialize_zeros (b : Std.Array U8 64#usize) (hb : b.val = List.replicate 64 0#u8) :
    deserializeUncompressed b = none := by
  unfold deserializeUncompressed
  rw [hb]
  decide

theorem leBytes32_zero : leBytes32 0 = List.replicate 32 0#u8 := by decide

theorem leBytes32_eq_zero {n : Nat} (hn : n < 256 ^ 32) (h : leBytes32 n = List.replicate 32 0#u8) :
    n = 0 := by
  have := leNat_leBytes32 n hn
  rw [h] at this
  rw [← this]; decide

/-! ## Decoding what `negate_g1` returns -/

theorem toArray64_eq {v : alloc.vec.Vec U8} {l : List U8} (hv : v.val = l) (hl : l.length = 64) :
    toArray64 v = some (Std.Array.from l (by simpa using hl)) := by
  unfold toArray64
  rw [dif_pos (by rw [hv]; exact hl)]
  simp [hv]

/-- **Negation is what it claims to be.** If `negate_g1(a)` returns `a'`, the
    syscalls read `a` as a point `P` and `a'` as `-P`. -/
theorem negateG1_decode {a a' : Std.Array U8 64#usize} (h : negateG1 a = ok (some a')) :
    ∃ P, syscallDecodeG1 a = some P ∧ syscallDecodeG1 a' = some P.neg := by
  unfold negateG1 at h
  obtain ⟨le, hle, h⟩ := bind_eq_ok' h
  obtain ⟨_, hce, hval⟩ := (WP.spec_equiv_exists _ _).mp (change_endianness_64 a)
  rw [hce, ok.injEq] at hle
  subst hle
  rw [toArray64_eq hval (by simp [reverseHalves])] at h
  rw [show ∀ x : Std.Array U8 64#usize, (some x >>= deserializeUncompressed) = deserializeUncompressed x
    from fun _ => rfl] at h
  split at h
  · simp at h
  · rename_i P hP
    obtain ⟨out, hout, h⟩ := bind_eq_ok' h
    obtain ⟨_, hce', hval'⟩ := (WP.spec_equiv_exists _ _).mp (change_endianness_64 P.neg.toBytes)
    rw [hce', ok.injEq] at hout
    subst hout
    rw [ok.injEq, toArray64_eq hval' (by simp [reverseHalves]), Option.some.injEq] at h
    have ha' : a'.val = reverseHalves P.neg.toBytes.val := by rw [← h]; simp
    have hdecA : syscallDecodeG1 a = some P := by
      unfold syscallDecodeG1
      rw [if_neg]
      · exact hP
      · intro hz
        rw [deserialize_zeros _ (by simp [hz, reverseHalves])] at hP
        simp at hP
    refine ⟨P, hdecA, ?_⟩
    rcases deserialize_some hP with rfl | ⟨hinf, hc⟩
    · -- the identity: negation encodes it as all zeros, which the syscall reads as the identity
      have hz : a'.val = List.replicate 64 0#u8 := by
        rw [ha']
        simp [G1Affine.neg, G1Affine.toBytes, leBytes32_zero, reverseHalves]
      simp [syscallDecodeG1, hz, G1Affine.neg]
    · -- a point on the curve: its negation is too, and decodes from its own encoding
      have hinf' : P.neg.infinity = false := hinf
      have hon : P.neg.y ^ 2 = P.neg.x ^ 3 + 3 := by simp [G1Affine.neg, hc]
      have hlen : P.neg.toBytes.val.length = 64 := by simp
      unfold syscallDecodeG1
      rw [if_neg]
      · have : (Std.Array.from (reverseHalves a'.val) (reverseHalves_length a') : Std.Array U8 64#usize) =
            P.neg.toBytes := by
          rw [Std.Array.eq_iff]; simp [ha', reverseHalves_involutive _ hlen]
        rw [this, deserialize_toBytes _ hinf' hon]
      · -- the encoding of a curve point is not all zeros
        intro hz
        have hb : P.neg.toBytes.val = List.replicate 64 0#u8 := by
          rw [← reverseHalves_involutive _ hlen, ← ha', hz]; decide
        have hx : P.x.val = 0 := by
          apply leBytes32_eq_zero (lt_trans (ZMod.val_lt _) (lt_trans q_lt (by norm_num)))
          have := congrArg (List.take 32) hb
          simpa [G1Affine.toBytes, G1Affine.neg, List.take_append_of_le_length, leBytes32_length] using this
        have hy : (-P.y).val = 0 := by
          apply leBytes32_eq_zero (lt_trans (ZMod.val_lt _) (lt_trans q_lt (by norm_num)))
          have := congrArg (List.drop 32) hb
          simpa [G1Affine.toBytes, G1Affine.neg, List.drop_append_of_le_length, leBytes32_length] using this
        rw [ZMod.val_eq_zero] at hx hy
        rw [neg_eq_zero] at hy
        rw [hx, hy] at hc
        exact three_ne_zero (by simpa using hc.symm)

end PrivacyCash.Proofs.G1
