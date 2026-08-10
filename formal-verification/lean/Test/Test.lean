import Mathlib.Data.ZMod.Basic

def BitString (L: ℕ): Type := Vector (ZMod 2) L

namespace BitString

def xor {L: ℕ} (x y: BitString L): (BitString L) :=
    -- TODO define f
    Vector.zipWith (fun a b => a + b) x y


lemma xor_comm_property {L: ℕ} (x y : BitString L): xor x y = xor y x :=
    by
        apply Vector.ext
        intro i h_i_lt_L
        simp[xor]
        simp[add_comm]

lemma xor_assoc_property {L: ℕ} (x y z: BitString L): xor x (xor y z) = xor (xor x y) z :=
    by
        apply Vector.ext
        intro i h_i_lt_L
        simp[xor]
        simp[add_assoc]

#eval (Vector.replicate 5 0: BitString 5)

def BitString_ID {L: ℕ} : BitString L := Vector.replicate L 0

lemma xor_show_identity {L: ℕ} (x: BitString L): xor x BitString_ID = x :=
    Vector.ext fun i i_less_than_L => by simp [xor, BitString_ID]


lemma xor_self_inverse {L: ℕ} (x: BitString L): xor x x = BitString_ID :=
    by
        apply Vector.ext
        intro i i_less_than_L
        simp[xor, BitString_ID]
        exact CharTwo.add_eq_zero.mpr rfl

end BitString


structure ShannonCipher (K M C: Type) where
    enc: K → M → C
    dec: K → C → M
    correctness: ∀ (k: K) (m: M), dec k (enc k m) = m

open BitString

def OneTimePad (L: ℕ ) : ShannonCipher (BitString L) (BitString L) (BitString L) :=
    {
        enc := fun k m => xor k m,
        dec := fun k c => xor k c,
        correctness := by
            simp[xor_assoc_property]
            simp[xor_self_inverse]
            simp[xor_comm_property]
            simp[xor_show_identity]
    }
