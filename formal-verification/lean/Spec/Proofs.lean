import Spec.Vocabulary

/-! # Proofs (not for review)

All lemmas and the proofs of the theorems stated in `Spec/Statements.lean`. Lean checks
them; reviewers don't need to read this file. -/

namespace LeanSpec
open PoseidonHashes Sha

variable [PoseidonHashes] [Sha] [Groups]
variable [AddCommGroup G1] [Module F G1] [AddCommGroup G2] [Module F G2] [CommGroup GT]
variable [Pairing] [Deployment]

--/////////////////////////////////////////
-- Supporting lemmas. Not for review: they only serve the proofs below.
--/////////////////////////////////////////

-- LEMMA (used by G1b): one `transact` step strictly grows the nullifier set.
lemma nullifier_set_monotonicity_step
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h: transact inputs oldWorld newWorld)
  : oldWorld.state.nullifiers ⊂ newWorld.state.nullifiers := by
  -- Direct proof: unfold `transact`, then hand back `inputs.k0` as the witness element that's
  -- in `newWorld` but not `oldWorld`.
  -- `transact` gives us that `newWorld` is exactly `transactEffects inputs oldWorld`, and its
  -- preconditions guarantee `k0` is a fresh nullifier, absent from `oldWorld`.
  obtain ⟨hpre, hagree⟩ := h
  have hk0New : inputs.k0 ∉ oldWorld.state.nullifiers := hpre.newNullifiers.1
  -- the new nullifier set is the one `transactEffects` predicts
  rw [hagree.nullifiers]
  simp only [transactEffects, transferEffects]
  split_ifs <;>
    exact (Finset.ssubset_iff_of_subset Finset.subset_union_left).mpr
      ⟨inputs.k0, Finset.mem_union_right _ (Finset.mem_insert_self _ _), hk0New⟩


-- LEMMA (used by G1b): the same note (amount, secret key, blinding, mint) at the same leaf
-- index gives the same nullifier. Secret keys are compared directly: two keys could share
-- a public key `H1 sk` if `H1` collides.
lemma same_note_same_nullifier
  (witness1 witness2: Witness)
  (pubInput1 pubInput2: PubInputs)
  (h1: RelationS pubInput1 witness1)
  (h2: RelationS pubInput2 witness2)
  (i i': Fin 2)
  (h3: witness1.inAmt i = witness2.inAmt i'
    ∧ witness1.inSk i = witness2.inSk i'
    ∧ witness1.inR i = witness2.inR i'
    ∧ witness1.mint = witness2.mint
    ∧ (witness1.openings i).index = (witness2.openings i').index)
  : pubInput1.nullifiers i = pubInput2.nullifiers i' := by
  obtain ⟨hAmt, hSk, hR, hMint, hIdx⟩ := h3
  have hPk : witness1.inPk i = witness2.inPk i' := by
    simp only [Witness.inPk, hSk]
  have hC : witness1.inC i = witness2.inC i' := by
    simp only [Witness.inC, commit, hAmt, hPk, hR, hMint]
  have hSign : witness1.sign i = witness2.sign i' := by
    simp only [Witness.sign, signature, hSk, hC, hIdx]
  rw [h1.nullifierCorrectness i, h2.nullifierCorrectness i']
  simp only [nullifier, hC, hIdx, hSign]


-- LEMMA (used by G1b): the same commitment at the same leaf index gives the same nullifier,
-- or an `H1` collision (secret keys) or an `H4` collision (note contents).
lemma same_commitment_same_nullifier_or_collision
  (witness1 witness2: Witness)
  (pubInput1 pubInput2: PubInputs)
  (h1: RelationS pubInput1 witness1)
  (h2: RelationS pubInput2 witness2)
  (i i': Fin 2)
  (sameIndex: (witness1.openings i).index = (witness2.openings i').index)
  (sameCommitment: witness1.inC i = witness2.inC i')
  : pubInput1.nullifiers i = pubInput2.nullifiers i'
    ∨ H1Collision (witness1.inSk i) (witness2.inSk i')
    ∨ H4Collision ⟨witness1.inAmt i, witness1.inPk i, witness1.inR i, witness1.mint⟩
                  ⟨witness2.inAmt i', witness2.inPk i', witness2.inR i', witness2.mint⟩ := by
  have hCommitEq : commit (witness1.inAmt i) (witness1.inPk i) (witness1.inR i) witness1.mint
      = commit (witness2.inAmt i') (witness2.inPk i') (witness2.inR i') witness2.mint :=
    sameCommitment
  rcases commitment_determines_value_or_collision _ _ _ _ _ _ _ _ hCommitEq with hTupleEq | hH4
  · simp only [Note.mk.injEq] at hTupleEq
    obtain ⟨hAmt, hPk, hR, hMint⟩ := hTupleEq
    by_cases hSk : witness1.inSk i = witness2.inSk i'
    · exact Or.inl (same_note_same_nullifier witness1 witness2 pubInput1 pubInput2 h1 h2 i i'
        ⟨hAmt, hSk, hR, hMint, sameIndex⟩)
    · have hPkH1 : H1 (witness1.inSk i) = H1 (witness2.inSk i') := hPk
      exact Or.inr (Or.inl ⟨hSk, hPkH1⟩)
  · exact Or.inr (Or.inr hH4)


-- LEMMA: `moveLamports` in ℤ, when the source can pay.
lemma moveLamports_apply (b : Pubkey → ℕ) (src dst : Pubkey) (x : ℕ) (hsd : src ≠ dst)
    (hx : x ≤ b src) (k : Pubkey) :
    (moveLamports b src dst x k : ℤ)
      = b k - (if k = src then (x : ℤ) else 0) + (if k = dst then (x : ℤ) else 0) := by
  unfold moveLamports
  by_cases hkd : k = dst
  · rw [hkd, Function.update_self, Function.update_of_ne (Ne.symm hsd), if_neg (Ne.symm hsd),
      if_pos rfl]
    push_cast; ring
  · rw [Function.update_of_ne hkd, if_neg hkd]
    by_cases hks : k = src
    · rw [hks, Function.update_self, if_pos rfl, Nat.cast_sub hx]; ring
    · rw [Function.update_of_ne hks, if_neg hks]; ring

-- LEMMA: the effect functions leave the state (tree, nullifiers, pool address, config) to
-- `transactEffects`.
@[simp] lemma nullifierRentEffects_state (inputs: TxInputs) (w: World) :
    (nullifierRentEffects inputs w).state = w.state := rfl

lemma transferEffects_state (inputs: TxInputs) (w: World) :
    (transferEffects inputs w).state = w.state := by
  unfold transferEffects; split_ifs <;> rfl

-- LEMMA (used by G1c, G3a, G4a, G4b): the predicted world moves every account by exactly
-- `balanceDelta`. The solvency preconditions rule out ℕ underflow; `poolIsSeparate` keeps
-- the pool's role apart from the paid roles.
lemma transactEffects_balances (inputs : TxInputs) (old : World)
    (hSolv : signerSolvent old.balances inputs.s inputs.extAmt old.nullifierRent)
    (hPool : poolSolvent old.poolBalance old.rentExemptMin inputs.extAmt inputs.f)
    (hSep : poolIsSeparate inputs old.state.pool) (k : Pubkey) :
    ((transactEffects inputs old).balances k : ℤ)
      = old.balances k + balanceDelta inputs old.state.pool old.nullifierRent k := by
  obtain ⟨hsP, hAP, htP⟩ := hSep
  obtain ⟨hPw, hPd⟩ := hPool
  unfold signerSolvent at hSolv
  unfold World.poolBalance at hPw hPd
  set P := old.state.pool with hP
  set w0 := nullifierRentEffects inputs old with hw0
  set w1 := transferEffects inputs w0 with hw1
  have hw0P : w0.state.pool = P := by rw [hw0, nullifierRentEffects_state]
  have hw1P : w1.state.pool = P := by rw [hw1, transferEffects_state, hw0P]
  -- the rent step
  have hrent : ∀ x, (w0.balances x : ℤ) = old.balances x
      - (if x = inputs.s then 2 * (old.nullifierRent : ℤ) else 0) := by
    intro x
    simp only [hw0, nullifierRentEffects]
    by_cases hxs : x = inputs.s
    · rw [hxs, Function.update_self, if_pos rfl]
      have : 2 * old.nullifierRent ≤ old.balances inputs.s := by split_ifs at hSolv <;> omega
      rw [Nat.cast_sub this]; push_cast; ring
    · rw [Function.update_of_ne hxs, if_neg hxs]; ring
  have hw0Pv : (w0.balances P : ℤ) = old.balances P := by
    rw [hrent P, if_neg (Ne.symm hsP)]; ring
  -- the transfer step
  have htr : ∀ x, (w1.balances x : ℤ) = w0.balances x
      + (if x = inputs.A ∧ inputs.extAmt < 0 then (inputs.extAmt.natAbs : ℤ) else 0)
      - (if x = inputs.s ∧ inputs.extAmt > 0 then inputs.extAmt else 0)
      + (if x = P then inputs.extAmt else 0) := by
    intro x
    simp only [hw1, transferEffects]
    by_cases hz : inputs.extAmt = 0
    · simp [hz]
    · by_cases hpos : inputs.extAmt > 0
      · have habs : (inputs.extAmt.natAbs : ℤ) = inputs.extAmt := Int.natAbs_of_nonneg (le_of_lt hpos)
        have hcan : inputs.extAmt.natAbs ≤ w0.balances inputs.s := by
          have h1 := hrent inputs.s
          rw [if_pos rfl] at h1
          rw [if_pos hpos] at hSolv
          omega
        simp only [hz, if_false, hpos, if_true]
        rw [hw0P, moveLamports_apply _ _ _ _ hsP hcan, habs]
        by_cases hxs : x = inputs.s <;> by_cases hxP : x = P <;>
          simp [hxs, hxP, hsP, not_lt.mpr (le_of_lt hpos)] <;> (try ring)
      · have hneg : inputs.extAmt < 0 := by omega
        have habs : (inputs.extAmt.natAbs : ℤ) = -inputs.extAmt := by omega
        have hcan : inputs.extAmt.natAbs ≤ w0.balances P := by
          have h1 := hPw hneg
          have h2 := hw0Pv
          rw [abs_of_neg hneg] at h1
          omega
        simp only [hz, if_false, hpos]
        have hAP' := hAP hneg
        rw [hw0P, moveLamports_apply _ _ _ _ (Ne.symm hAP') hcan, habs]
        by_cases hxA : x = inputs.A <;> by_cases hxP : x = P <;>
          simp [hxA, hxP, hAP', hneg] <;> (try ring)
  -- the fee step
  have hfee : inputs.f ≤ w1.balances P := by
    have h1 := htr P
    rw [if_neg (fun h => hAP h.2 h.1.symm), if_neg (fun h => hsP (h.1.symm)), if_pos rfl, hw0Pv] at h1
    by_cases hneg : inputs.extAmt < 0
    · have := hPw hneg; rw [abs_of_neg hneg] at this; omega
    · rcases Nat.eq_zero_or_pos inputs.f with hf0 | hfpos
      · omega
      · have := hPd ⟨by omega, hfpos⟩; omega
  show (moveLamports w1.balances w1.state.pool inputs.t inputs.f k : ℤ) = _
  rcases Nat.eq_zero_or_pos inputs.f with hf0 | hfpos
  · -- no fee: nothing moves, whoever the fee recipient is
    have hm : moveLamports w1.balances w1.state.pool inputs.t inputs.f k = w1.balances k := by
      simp only [moveLamports, hf0, Nat.sub_zero, Nat.add_zero, Function.update_eq_self]
    rw [hm, htr k, hrent k]
    unfold balanceDelta
    split_ifs <;> simp_all <;> ring
  · rw [hw1P, moveLamports_apply _ _ _ _ (Ne.symm (htP hfpos)) hfee, htr k, hrent k]
    unfold balanceDelta
    split_ifs <;> ring

-- LEMMA (used by G4a, G1c): one `transact` step moves the pool's SOL by exactly `extAmt − f`.
lemma sol_balance_correctness_step
  (oldWorld newWorld : World)
  (inputs: TxInputs)
  (h1: transact inputs oldWorld newWorld)
  : (newWorld.poolBalance : ℤ) = oldWorld.poolBalance + inputs.extAmt - inputs.f
  := by
  obtain ⟨hpre, heff⟩ := h1
  obtain ⟨hsP, hAP, htP⟩ := hpre.poolSeparate
  have hpool : newWorld.state.pool = oldWorld.state.pool := by
    rw [heff.pool]; simp only [transactEffects, transferEffects_state, nullifierRentEffects_state]
  unfold World.poolBalance
  rw [hpool, heff.balances, transactEffects_balances inputs oldWorld hpre.signerSolvency
    hpre.poolSolvency hpre.poolSeparate]
  unfold balanceDelta
  have hA : ¬ (oldWorld.state.pool = inputs.A ∧ inputs.extAmt < 0) := fun h => hAP h.2 h.1.symm
  have hs1 : ¬ (oldWorld.state.pool = inputs.s ∧ inputs.extAmt > 0) := fun h => hsP h.1.symm
  have hs2 : ¬ (oldWorld.state.pool = inputs.s) := fun h => hsP h.symm
  rw [if_neg hA, if_neg hs1, if_neg hs2, if_pos rfl]
  rcases Nat.eq_zero_or_pos inputs.f with hf0 | hfpos
  · simp [hf0]
  · rw [if_neg (fun h => htP hfpos h.symm)]; ring

/-- HELPER (used by `Connection/Reachable.lean`): trace-free form of `Run.poolBalance`.
    Weaker: `∃ txs` alone could be any list with the right sum. -/
lemma sol_balance_correctness
  (params : InitParams) (w: World)
  (h: ReachableWorld (initWorld params) w)
  : ∃ txs: List TxInputs,
      (w.poolBalance : ℤ)
        = txs.foldl (fun acc (tx: TxInputs) => acc + tx.extAmt - tx.f) (params.rentExemptMin : ℤ) := by
  induction h with
  | noStep => exact ⟨[], by simp [initWorld, World.poolBalance]⟩
  | extend inputs _ transact_proof ih =>
    obtain ⟨txs, htxs⟩ := ih
    refine ⟨txs ++ [inputs], ?_⟩
    have hstep := sol_balance_correctness_step _ _ inputs transact_proof
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep, htxs]

/-- HELPER: `transferEffects` doesn't touch the tree. -/
lemma transferEffects_tree (inputs: TxInputs) (oldWorld: World) :
    (transferEffects inputs oldWorld).state.tree = oldWorld.state.tree := by
  unfold transferEffects
  split_ifs <;> rfl


/-- HELPER: a value in the range of `Function.update f i v` is `v`, or was already in
    the range of `f`. -/
lemma mem_range_update_or_mem_range {α β} [DecidableEq α] (f: α → β) (i: α) (v y: β)
    (h: y ∈ Set.range (Function.update f i v)) : y = v ∨ y ∈ Set.range f := by
  obtain ⟨x, hx⟩ := h
  rw [Function.update_apply] at hx
  split_ifs at hx with hxi
  · exact Or.inl hx.symm
  · exact Or.inr ⟨x, hx⟩

/-- HELPER: `appendEffects` writes its new root into the next `history` slot. -/
lemma appendEffects_history (c: F) (t: Tree) :
    (appendEffects c t).history
      = Function.update t.history (t.rootIndex + 1) (appendEffects c t).root := rfl

/-- HELPER: `nextIndex` of `foldAppend cs initTree` is `cs.length`. -/
lemma foldAppend_nextIndex (cs : List F) : (foldAppend cs initTree).nextIndex = cs.length := by
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y ih =>
    have : foldAppend (ys ++ [y]) initTree = appendEffects y (foldAppend ys initTree) := by
      simp [foldAppend]
    rw [this]
    show (foldAppend ys initTree).nextIndex + 1 = (ys ++ [y]).length
    rw [ih]; simp


-- Merkle position binding (used by G1a and G3a). `Opening.Valid` only says a path hashes to
-- the root, not that `leaf` is what the tree holds at `index`. Extraction
-- (`opening_extractable_or_collision`): a valid opening's leaf is the real leaf at its
-- index, or an `H2` collision (`PathCollision`). Preservation
-- (`opening_forward_preservation`): a written leaf keeps a valid opening as leaves are added.


lemma foldUpTo_congr {α : Type} : ∀ (n : ℕ) {f f' : α → ℕ → α} (x : α),
    (∀ y k, k < n → f y k = f' y k) → foldUpTo f n x = foldUpTo f' n x
  | 0, _, _, x, _ => by simp [foldUpTo]
  | (n+1), f, f', x, hh => by
    show f (foldUpTo f n x) n = f' (foldUpTo f' n x) n
    rw [foldUpTo_congr n x (fun y k hk => hh y k (Nat.lt_succ_of_lt hk))]
    exact hh _ n (Nat.lt_succ_self n)

lemma fin_foldl_eq_foldUpTo {α : Type} :
    ∀ (n : ℕ) (g : α → Fin n → α) (x : α),
      Fin.foldl n g x = foldUpTo (fun x h => if hh : h < n then g x ⟨h, hh⟩ else x) n x
  | 0, g, x => by simp [foldUpTo]
  | (n+1), g, x => by
    rw [Fin.foldl_succ_last]
    have ih := fin_foldl_eq_foldUpTo n (fun x (i : Fin n) => g x i.castSucc) x
    rw [ih]
    have hagree : ∀ (y : α) (k : ℕ), k < n →
        (fun x h => if hh : h < n then g x (⟨h, hh⟩ : Fin n).castSucc else x) y k
        = (fun x h => if hh : h < n+1 then g x ⟨h, hh⟩ else x) y k := by
      intro y k hk
      simp only [dif_pos hk, dif_pos (Nat.lt_succ_of_lt hk), Fin.castSucc_mk]
    rw [foldUpTo_congr n x hagree]
    show g (foldUpTo (fun x h => if hh : h < n+1 then g x ⟨h,hh⟩ else x) n x) (Fin.last n)
       = foldUpTo (fun x h => if hh : h < n+1 then g x ⟨h,hh⟩ else x) (n+1) x
    simp only [foldUpTo, dif_pos (Nat.lt_succ_self n)]
    rfl

/-- `fin_foldl_eq_foldUpTo` for an `f` that agrees with `g` pointwise. -/
lemma fin_foldl_eq_foldUpTo_plain {α : Type} {n : ℕ} (g : α → Fin n → α) (f : α → ℕ → α)
    (hagree : ∀ x (h : ℕ) (hh : h < n), f x h = g x ⟨h, hh⟩) (x : α) :
    Fin.foldl n g x = foldUpTo f n x := by
  rw [fin_foldl_eq_foldUpTo n g x]
  apply foldUpTo_congr
  intro y k hk
  rw [dif_pos hk, hagree y k hk]

-- HELPER: small `Nat.testBit`/`>>>` facts the carry-propagation arguments below rely on.

lemma testBit_shiftRight_eq (k h : ℕ) : Nat.testBit k h = decide ((k >>> h) % 2 = 1) := by
  rw [← Nat.testBit_zero (k >>> h), Nat.testBit_shiftRight, Nat.add_zero]

lemma shiftRight_succ_eq (k h : ℕ) : k >>> h = 2 * (k >>> (h+1)) + (k >>> h) % 2 := by
  rw [Nat.shiftRight_succ]; omega

lemma div_two_shiftRight (n h : ℕ) : n >>> (h+1) = (n / 2) >>> h := by
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, pow_succ, Nat.div_div_eq_div_mul,
      Nat.mul_comm]

/-- Binary increment: if bit `h` of `n+1` is set, either it was already set (and the
    height-`h` block index is unchanged), or it was just flipped (and the index moves up
    by one). -/
lemma testBit_succ_cases : ∀ (h n : ℕ), Nat.testBit (n+1) h = true →
    (Nat.testBit n h = true ∧ (n+1) >>> h = n >>> h)
    ∨ (Nat.testBit n h = false ∧ (n+1) >>> h = n >>> h + 1)
  | 0, n, hb => by
    right
    have h0 : Nat.testBit n 0 = decide (n % 2 = 1) := Nat.testBit_zero n
    have h1 : Nat.testBit (n+1) 0 = decide ((n+1) % 2 = 1) := Nat.testBit_zero (n+1)
    rw [h1] at hb
    refine ⟨?_, by simp⟩
    rw [h0]
    simp only [decide_eq_true_eq] at hb
    simp only [decide_eq_false_iff_not]
    omega
  | (h+1), n, hb => by
    rw [Nat.testBit_succ] at hb
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- `n` even: incrementing only ever touches bit 0, so bit `h+1` (and everything at
      -- or above it) is untouched -- `(n+1)/2 = n/2`, so the recursion doesn't even fire.
      have hnd : n / 2 = m := by omega
      have hn1d : (n+1) / 2 = m := by omega
      rw [hn1d] at hb
      rw [Nat.testBit_succ, hnd]
      exact Or.inl ⟨hb, by rw [div_two_shiftRight, div_two_shiftRight, hnd, hn1d]⟩
    · -- `n` odd: bit 0 carries, so whether bit `h+1` (and above) changes reduces to the
      -- same question one level down, for `n/2`.
      have hnd : n / 2 = m := by omega
      have hn1d : (n+1) / 2 = m + 1 := by omega
      rw [hn1d] at hb
      rw [Nat.testBit_succ, hnd]
      rcases testBit_succ_cases h m hb with ⟨hbt, hs⟩ | ⟨hbf, hs⟩
      · exact Or.inl ⟨hbt, by rw [div_two_shiftRight, div_two_shiftRight, hnd, hn1d]; exact hs⟩
      · exact Or.inr ⟨hbf, by rw [div_two_shiftRight, div_two_shiftRight, hnd, hn1d]; exact hs⟩

lemma div_mul_le (n h : ℕ) : (n >>> h) * 2^h ≤ n := by
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.div_mul_le_self n (2^h)

/-- The block after leaf `n`'s height-`h` block starts after position `n`. -/
lemma succ_le_shiftRight_succ_mul (n h : ℕ) : n + 1 ≤ (n >>> h + 1) * 2^h := by
  rw [Nat.shiftRight_eq_div_pow]
  have hpos : 0 < 2^h := Nat.two_pow_pos h
  have hmod : n % 2^h < 2^h := Nat.mod_lt _ hpos
  have hdm : n / 2^h * 2^h + n % 2^h = n := by
    rw [Nat.mul_comm]; exact Nat.div_add_mod n (2^h)
  have hkey : (n/2^h + 1) * 2^h = n/2^h*2^h + 2^h := by ring
  rw [hkey]
  omega

-- HELPER: `treeHash` under appending: a block inside the old list doesn't change
-- (`treeHash_ext`), and a block past the end is the zero hash (`treeHash_zero`).

lemma leafAt_append_left (cs extra : List F) (i : ℕ) (h : i < cs.length) :
    leafAt (cs ++ extra) i = leafAt cs i := by
  unfold leafAt
  have hlen : (cs ++ extra).length = cs.length + extra.length := by simp
  rw [dif_pos (by omega : i < (cs ++ extra).length), dif_pos h, List.getElem_append_left h]

lemma leafAt_own (cs : List F) (y : F) : leafAt (cs ++ [y]) cs.length = y := by
  unfold leafAt
  rw [dif_pos (by simp : cs.length < (cs ++ [y]).length)]
  simp

lemma treeHash_ext (cs extra : List F) : ∀ (h idx : ℕ), (idx+1) * 2^h ≤ cs.length →
    treeHash (cs ++ extra) h idx = treeHash cs h idx
  | 0, idx, hb => by
    simp only [treeHash]
    apply leafAt_append_left
    omega
  | h+1, idx, hb => by
    simp only [treeHash]
    have hkey : (idx+1)*2^(h+1) = (2*idx+2)*2^h := by ring
    rw [hkey] at hb
    have hleft : (2*idx+1) * 2^h ≤ cs.length :=
      le_trans (Nat.mul_le_mul_right _ (by omega)) hb
    have hright : (2*idx+1+1) * 2^h ≤ cs.length := by
      rw [show 2*idx+1+1 = 2*idx+2 from rfl]; exact hb
    rw [treeHash_ext cs extra h (2*idx) hleft, treeHash_ext cs extra h (2*idx+1) hright]

lemma treeHash_zero (cs : List F) : ∀ (h idx : ℕ), cs.length ≤ idx * 2^h →
    treeHash cs h idx = Z h
  | 0, idx, hb => by
    simp only [treeHash, leafAt]
    rw [dif_neg (by omega)]
  | h+1, idx, hb => by
    simp only [treeHash, Z]
    have hkey : idx * 2^(h+1) = (2*idx) * 2^h := by ring
    rw [hkey] at hb
    have h1 : cs.length ≤ (2*idx) * 2^h := hb
    have h2 : cs.length ≤ (2*idx+1) * 2^h := by
      have hkey2 : (2*idx+1)*2^h = (2*idx)*2^h + 2^h := by ring
      rw [hkey2]
      exact le_trans h1 (Nat.le_add_right _ _)
    rw [treeHash_zero cs h (2*idx) h1, treeHash_zero cs h (2*idx+1) h2]

-- HELPER: the canonical opening of any `k` hashes to the tree's root (pure path
-- arithmetic, independent of `appendEffects`).

lemma calcRoot_canonicalOpening_aux (cs : List F) (k : ℕ) :
    ∀ H : ℕ, foldUpTo (fun acc h =>
        if Nat.testBit k h then H2 (treeHash cs h (siblingIdx k h)) acc
        else H2 acc (treeHash cs h (siblingIdx k h))) H (leafAt cs k)
      = treeHash cs H (k >>> H) := by
  intro H
  induction H with
  | zero => simp [foldUpTo, treeHash]
  | succ H ih =>
    show (fun acc h =>
        if Nat.testBit k h then H2 (treeHash cs h (siblingIdx k h)) acc
        else H2 acc (treeHash cs h (siblingIdx k h)))
      (foldUpTo (fun acc h =>
        if Nat.testBit k h then H2 (treeHash cs h (siblingIdx k h)) acc
        else H2 acc (treeHash cs h (siblingIdx k h))) H (leafAt cs k)) H
      = treeHash cs (H+1) (k >>> (H+1))
    rw [ih]
    have htb := testBit_shiftRight_eq k H
    have hshift := shiftRight_succ_eq k H
    show (if Nat.testBit k H then H2 (treeHash cs H (siblingIdx k H)) (treeHash cs H (k >>> H))
          else H2 (treeHash cs H (k >>> H)) (treeHash cs H (siblingIdx k H)))
       = H2 (treeHash cs H (2*(k >>> (H+1)))) (treeHash cs H (2*(k >>> (H+1))+1))
    by_cases hb : Nat.testBit k H = true
    · have h2 : (k >>> H) % 2 = 1 := of_decide_eq_true (htb.symm.trans hb)
      have hidx : siblingIdx k H = 2 * (k >>> (H+1)) := by
        unfold siblingIdx; rw [if_pos hb]; omega
      have hown : k >>> H = 2 * (k >>> (H+1)) + 1 := by omega
      simp only [hb, if_true, hidx, hown]
    · have hbf : Nat.testBit k H = false := by simpa using hb
      have h2 : (k >>> H) % 2 ≠ 1 := of_decide_eq_false (htb.symm.trans hbf)
      have hidx : siblingIdx k H = 2 * (k >>> (H+1)) + 1 := by
        unfold siblingIdx; rw [if_neg hb]; omega
      have hown : k >>> H = 2 * (k >>> (H+1)) := by omega
      simp [hbf, hidx, hown]

lemma calcRoot_canonicalOpening (cs : List F) (k : Fin (2^26)) :
    (canonicalOpening cs k).calcRoot (leafAt cs k.val) = treeHash cs 26 0 := by
  unfold Opening.calcRoot
  rw [fin_foldl_eq_foldUpTo_plain _
    (fun acc h => if Nat.testBit k.val h then H2 (treeHash cs h (siblingIdx k.val h)) acc
        else H2 acc (treeHash cs h (siblingIdx k.val h)))
    (by intro x h hh; simp [canonicalOpening, Opening.accIsRight])]
  have haux := calcRoot_canonicalOpening_aux cs k.val 26
  have hk0 : (k:ℕ) >>> 26 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt k.isLt
  rw [hk0] at haux
  exact haux

-- HELPER: `appendEffects` is correct: appending `y` gives the `treeHash` root, and
-- updates exactly the right `subtrees` slots, each to its completed block (the standard
-- incremental Merkle tree invariant, proved rather than assumed).

/-- `appendEffects`'s per-height loop body, with `nextIndex` abstracted to `n`. -/
def appendBody (n : ℕ) : (F × (Fin 26 → F)) → Fin 26 → (F × (Fin 26 → F)) :=
  fun (current, subtrees) height =>
    if Nat.testBit n height.val then (H2 (subtrees height) current, subtrees)
    else (H2 current (Z height.val), Function.update subtrees height current)

def appendBodyN (n : ℕ) : (F × (Fin 26 → F)) → ℕ → (F × (Fin 26 → F)) :=
  fun x h => if hh : h < 26 then appendBody n x ⟨h, hh⟩ else x

lemma appendEffects_eq (c : F) (t : Tree) :
    (appendEffects c t).root = (Fin.foldl 26 (appendBody t.nextIndex) (c, t.subtrees)).1
    ∧ (appendEffects c t).subtrees = (Fin.foldl 26 (appendBody t.nextIndex) (c, t.subtrees)).2 := by
  constructor <;> rfl

/-- Loop invariant of `appendEffects` after the first `H ≤ 26` heights: the running hash
    is the block containing position `n`; each processed slot (`h < H`) is unchanged if
    bit `h` of `n` is set, else holds the just-completed block; other slots are
    untouched. Used at `H = 26` below. -/
lemma appendFold_aux (n : ℕ) (cs : List F) (hcs : cs.length = n) (y : F)
    (subOld : Fin 26 → F)
    (hSubInv : ∀ h : Fin 26, Nat.testBit n h.val = true →
        subOld h = treeHash cs h.val (siblingIdx n h.val)) :
    ∀ H : ℕ, H ≤ 26 →
      (foldUpTo (appendBodyN n) H (y, subOld)).1 = treeHash (cs ++ [y]) H (n >>> H)
      ∧ (∀ h : Fin 26, h.val < H →
          (foldUpTo (appendBodyN n) H (y, subOld)).2 h
          = if Nat.testBit n h.val then subOld h else treeHash (cs++[y]) h.val (n >>> h.val))
      ∧ (∀ h : Fin 26, ¬ h.val < H → (foldUpTo (appendBodyN n) H (y, subOld)).2 h = subOld h) := by
  intro H
  induction H with
  | zero =>
    intro _
    refine ⟨?_, ?_, ?_⟩
    · show y = treeHash (cs ++ [y]) 0 (n >>> 0)
      rw [Nat.shiftRight_zero]
      show y = leafAt (cs ++ [y]) n
      rw [← hcs]
      exact (leafAt_own cs y).symm
    · intro h hh; omega
    · intro h _; rfl
  | succ H ih =>
    intro hHb
    obtain ⟨ihc, ih1, ih2⟩ := ih (by omega)
    have hHlt : H < 26 := by omega
    set cur := (foldUpTo (appendBodyN n) H (y, subOld)).1 with hcur_def
    set sub := (foldUpTo (appendBodyN n) H (y, subOld)).2 with hsub_def
    have hpair : foldUpTo (appendBodyN n) H (y, subOld) = (cur, sub) := by
      rw [hcur_def, hsub_def]
    have hstep : foldUpTo (appendBodyN n) (H+1) (y, subOld) = appendBody n (cur, sub) ⟨H, hHlt⟩ := by
      show appendBodyN n (foldUpTo (appendBodyN n) H (y, subOld)) H = _
      rw [hpair]
      unfold appendBodyN
      rw [dif_pos hHlt]
    have hboundOld : (n >>> H) * 2^H ≤ n := div_mul_le n H
    by_cases hb : Nat.testBit n H = true
    · -- absorb branch: the just-completed block at height `H` (`n`'s ancestor there)
      -- combines with the already-stored left sibling; `subtrees` doesn't change.
      have hsubH : sub ⟨H, hHlt⟩ = subOld ⟨H, hHlt⟩ := ih2 ⟨H, hHlt⟩ (by simp)
      have hfst : (appendBody n (cur, sub) ⟨H, hHlt⟩).1 = H2 (sub ⟨H,hHlt⟩) cur := by
        show (if Nat.testBit n H then (H2 (sub ⟨H,hHlt⟩) cur, sub)
              else (H2 cur (Z H), Function.update sub ⟨H,hHlt⟩ cur)).1 = H2 (sub ⟨H,hHlt⟩) cur
        rw [if_pos hb]
      have hsnd : (appendBody n (cur, sub) ⟨H, hHlt⟩).2 = sub := by
        show (if Nat.testBit n H then (H2 (sub ⟨H,hHlt⟩) cur, sub)
              else (H2 cur (Z H), Function.update sub ⟨H,hHlt⟩ cur)).2 = sub
        rw [if_pos hb]
      have hkey : n >>> H = 2 * (n >>> (H+1)) + 1 := by
        have hs := shiftRight_succ_eq n H
        have h2 : (n >>> H) % 2 = 1 :=
          of_decide_eq_true ((testBit_shiftRight_eq n H).symm.trans hb)
        omega
      have hkeySib : siblingIdx n H = 2 * (n >>> (H+1)) := by
        unfold siblingIdx; rw [if_pos hb]; omega
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep, hfst]
        rw [hsubH, hSubInv ⟨H,hHlt⟩ hb]
        show H2 (treeHash cs H (siblingIdx n H)) cur
           = H2 (treeHash (cs++[y]) H (2*(n >>> (H+1)))) (treeHash (cs++[y]) H (2*(n >>> (H+1))+1))
        rw [hkeySib]
        congr 1
        · have hbound : (2*(n >>> (H+1)) + 1) * 2^H ≤ cs.length := by
            rw [hcs, ← hkey]; exact hboundOld
          exact (treeHash_ext cs [y] H (2*(n >>> (H+1))) hbound).symm
        · rw [ihc, hkey]
      · intro h hh
        rw [hstep, hsnd]
        by_cases heq : h.val < H
        · exact ih1 h heq
        · have hval : h.val = H := by omega
          have hEq : h = (⟨H,hHlt⟩ : Fin 26) := Fin.ext hval
          subst hEq
          rw [hsubH]
          simp [hb]
      · intro h hh
        rw [hstep, hsnd]
        exact ih2 h (by omega)
    · -- store branch: the block at height `H` isn't complete yet -- `n`'s ancestor there
      -- becomes `subtrees`'s new value, padded with the zero hash above it.
      have hbf : Nat.testBit n H = false := by simpa using hb
      have hfst : (appendBody n (cur, sub) ⟨H, hHlt⟩).1 = H2 cur (Z H) := by
        show (if Nat.testBit n H then (H2 (sub ⟨H,hHlt⟩) cur, sub)
              else (H2 cur (Z H), Function.update sub ⟨H,hHlt⟩ cur)).1 = H2 cur (Z H)
        rw [if_neg (by simp [hbf])]
      have hsnd : (appendBody n (cur, sub) ⟨H, hHlt⟩).2 = Function.update sub ⟨H,hHlt⟩ cur := by
        show (if Nat.testBit n H then (H2 (sub ⟨H,hHlt⟩) cur, sub)
              else (H2 cur (Z H), Function.update sub ⟨H,hHlt⟩ cur)).2
              = Function.update sub ⟨H,hHlt⟩ cur
        rw [if_neg (by simp [hbf])]
      have hkey : n >>> H = 2 * (n >>> (H+1)) := by
        have hs := shiftRight_succ_eq n H
        have h2 : (n >>> H) % 2 ≠ 1 :=
          of_decide_eq_false ((testBit_shiftRight_eq n H).symm.trans hbf)
        omega
      have hlen : (cs++[y]).length = n+1 := by rw [← hcs]; simp
      have hzero : treeHash (cs++[y]) H (n>>>H+1) = Z H := by
        apply treeHash_zero
        rw [hlen]
        exact succ_le_shiftRight_succ_mul n H
      refine ⟨?_, ?_, ?_⟩
      · rw [hstep, hfst]
        show H2 cur (Z H) = H2 (treeHash (cs++[y]) H (2*(n >>> (H+1)))) (treeHash (cs++[y]) H (2*(n >>> (H+1))+1))
        rw [ihc, hkey]
        congr 1
        rw [← hkey]
        exact hzero.symm
      · intro h hh
        rw [hstep, hsnd]
        by_cases heq : h = (⟨H,hHlt⟩ : Fin 26)
        · subst heq
          rw [Function.update_self, ihc]
          simp [hbf]
        · rw [Function.update_of_ne heq]
          have hlt : h.val < H := by
            rcases Nat.lt_or_ge h.val H with h1 | h1
            · exact h1
            · exact absurd (Fin.ext (by omega : h.val = H)) heq
          exact ih1 h hlt
      · intro h hh
        rw [hstep, hsnd]
        have hne : h ≠ (⟨H,hHlt⟩:Fin 26) := fun heq => hh (heq ▸ Nat.lt_succ_self H)
        rw [Function.update_of_ne hne]
        exact ih2 h (by omega)

/-- `appendFold_aux` at `H = 26`, restated with the bits of the new length (via
    `testBit_succ_cases`), as `foldAppend_spec` needs. -/
lemma appendEffects_root_subtrees (cs : List F) (hcap : cs.length < 2^26) (y : F)
    (subOld : Fin 26 → F)
    (hSubInv : ∀ h : Fin 26, Nat.testBit cs.length h.val = true →
        subOld h = treeHash cs h.val (siblingIdx cs.length h.val)) :
    (Fin.foldl 26 (appendBody cs.length) (y, subOld)).1 = treeHash (cs ++ [y]) 26 0
    ∧ ∀ h : Fin 26, Nat.testBit (cs.length+1) h.val = true →
        (Fin.foldl 26 (appendBody cs.length) (y, subOld)).2 h
          = treeHash (cs++[y]) h.val (siblingIdx (cs.length+1) h.val) := by
  set n := cs.length with hcs
  have hbridge : Fin.foldl 26 (appendBody n) (y, subOld) = foldUpTo (appendBodyN n) 26 (y, subOld) :=
    fin_foldl_eq_foldUpTo 26 (appendBody n) (y, subOld)
  obtain ⟨haux1, haux2, _⟩ := appendFold_aux n cs rfl y subOld hSubInv 26 (le_refl 26)
  have hn0 : n >>> 26 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hcap
  constructor
  · rw [hbridge, haux1, hn0]
  · intro h hSucc
    rw [hbridge]
    rcases testBit_succ_cases h.val n hSucc with ⟨hbt, hshift⟩ | ⟨hbf, hshift⟩
    · have hval : (foldUpTo (appendBodyN n) 26 (y, subOld)).2 h = subOld h :=
        haux2 h h.isLt |>.trans (if_pos hbt)
      rw [hval, hSubInv h hbt]
      have hidxEq : siblingIdx n h.val = siblingIdx (n+1) h.val := by
        unfold siblingIdx
        rw [if_pos hbt, if_pos hSucc, hshift]
      rw [hidxEq]
      symm
      apply treeHash_ext
      rw [← hcs, ← hidxEq]
      have hsib : siblingIdx n h.val = n >>> h.val - 1 := by unfold siblingIdx; rw [if_pos hbt]
      rw [hsib]
      have hb1 : 1 ≤ n >>> h.val := by
        have h2 : (n >>> h.val) % 2 = 1 :=
          of_decide_eq_true ((testBit_shiftRight_eq n h.val).symm.trans hbt)
        rcases Nat.eq_zero_or_pos (n >>> h.val) with h0 | h0
        · rw [h0] at h2; simp at h2
        · exact h0
      have heq2 : n >>> h.val - 1 + 1 = n >>> h.val := by omega
      rw [heq2]
      exact div_mul_le n h.val
    · have hval : (foldUpTo (appendBodyN n) 26 (y, subOld)).2 h
          = treeHash (cs++[y]) h.val (n >>> h.val) :=
        haux2 h h.isLt |>.trans (if_neg (by simp [hbf]))
      rw [hval]
      congr 1
      unfold siblingIdx
      rw [if_pos hSucc, hshift]
      generalize n >>> h.val = m
      omega

/-- `foldAppend cs initTree` (with `cs.length < 2^26`) is the expected tree: `nextIndex`
    is `cs.length`, `root` is the `treeHash` root, and every `subtrees` slot
    `appendEffects` reads holds the right completed block. -/
lemma foldAppend_spec : ∀ cs : List F, cs.length < 2^26 →
    (foldAppend cs initTree).nextIndex = cs.length
    ∧ (foldAppend cs initTree).root = treeHash cs 26 0
    ∧ ∀ h : Fin 26, Nat.testBit cs.length h.val = true →
        (foldAppend cs initTree).subtrees h = treeHash cs h.val (siblingIdx cs.length h.val) := by
  intro cs
  induction cs using List.reverseRecOn with
  | nil =>
    intro _
    refine ⟨rfl, ?_, ?_⟩
    · show initTree.root = treeHash [] 26 0
      show Z 26 = treeHash [] 26 0
      exact (treeHash_zero [] 26 0 (by simp)).symm
    · intro h htb
      have hfalse : Nat.testBit 0 h.val = false := by simp
      simp [hfalse] at htb
  | append_singleton ys y ih =>
    intro hcap
    have hlenEq : (ys ++ [y]).length = ys.length + 1 := by simp
    have hcapY : ys.length < 2^26 := by rw [hlenEq] at hcap; omega
    obtain ⟨hNI, hRoot, hSub⟩ := ih hcapY
    have hT1 : foldAppend (ys++[y]) initTree = appendEffects y (foldAppend ys initTree) := by
      simp [foldAppend]
    obtain ⟨hR2, hS2⟩ := appendEffects_root_subtrees ys (hNI ▸ hcapY) y
      (foldAppend ys initTree).subtrees (hNI ▸ hSub)
    obtain ⟨hEr, hEs⟩ := appendEffects_eq y (foldAppend ys initTree)
    rw [hNI] at hEr hEs
    refine ⟨?_, ?_, ?_⟩
    · rw [hT1, hlenEq]
      show (foldAppend ys initTree).nextIndex + 1 = ys.length + 1
      rw [hNI]
    · rw [hT1, hEr, hR2]
    · intro h htb
      rw [hT1, hEs, hlenEq]
      rw [hlenEq] at htb
      exact hS2 h htb

-- HELPER: telescoping collision over the 26 levels: if two openings hash to the same
-- root, either the leaves are equal or the first level where they differ is an `H2`
-- collision.


lemma stepFn_eq (k : ℕ) (sib : ℕ → F) (acc : F) (h : ℕ) :
    stepFn k sib acc h = H2 (stepPair k sib acc h).1 (stepPair k sib acc h).2 := by
  unfold stepFn stepPair
  split_ifs <;> rfl

lemma telescope (k : ℕ) (sib1 sib2 : ℕ → F) (leaf1 leaf2 : F) : ∀ H : ℕ,
    foldUpTo (stepFn k sib1) H leaf1 = foldUpTo (stepFn k sib2) H leaf2 →
    (leaf1 = leaf2 ∧ ∀ h, h < H → sib1 h = sib2 h)
    ∨ ∃ h, h < H ∧ H2Collision
        (stepPair k sib1 (foldUpTo (stepFn k sib1) h leaf1) h)
        (stepPair k sib2 (foldUpTo (stepFn k sib2) h leaf2) h)
  | 0, heq => Or.inl ⟨heq, fun h hh => absurd hh (by omega)⟩
  | (H+1), heq => by
      have step_eq : stepFn k sib1 (foldUpTo (stepFn k sib1) H leaf1) H
                   = stepFn k sib2 (foldUpTo (stepFn k sib2) H leaf2) H := heq
      rw [stepFn_eq, stepFn_eq] at step_eq
      by_cases hpair : stepPair k sib1 (foldUpTo (stepFn k sib1) H leaf1) H
                      = stepPair k sib2 (foldUpTo (stepFn k sib2) H leaf2) H
      · -- the two `H2` argument pairs at this level agree: descend to level `H` via the
        -- induction hypothesis, then extend the agreement by this level's siblings too.
        have hacc : foldUpTo (stepFn k sib1) H leaf1 = foldUpTo (stepFn k sib2) H leaf2
            ∧ sib1 H = sib2 H := by
          unfold stepPair at hpair
          split_ifs at hpair with hb
          · exact ⟨(Prod.ext_iff.mp hpair).2, (Prod.ext_iff.mp hpair).1⟩
          · exact ⟨(Prod.ext_iff.mp hpair).1, (Prod.ext_iff.mp hpair).2⟩
        rcases telescope k sib1 sib2 leaf1 leaf2 H hacc.1 with ⟨hL, hS⟩ | ⟨h0, hh0, hcol⟩
        · refine Or.inl ⟨hL, fun h hh => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hh with hh' | hh'
          · exact hS h hh'
          · rw [hh']; exact hacc.2
        · exact Or.inr ⟨h0, by omega, hcol⟩
      · -- the pairs disagree yet combined to the same `H2` output: a collision, right here.
        exact Or.inr ⟨H, by omega, ⟨hpair, step_eq⟩⟩

-- LEMMA (used by G1a): extraction. A valid opening's leaf is what `cs` holds at its index
-- (the zero leaf if unwritten), or the two paths give a `PathCollision`.


lemma calcRoot_eq_foldUpTo (O : Opening) (leaf : F) :
    O.calcRoot leaf = foldUpTo (stepFn O.index.val (OpeningSib O)) 26 leaf := by
  unfold Opening.calcRoot
  apply fin_foldl_eq_foldUpTo_plain
  intro x h hh
  unfold stepFn OpeningSib Opening.accIsRight
  rw [dif_pos hh]


lemma opening_extractable_or_collision
    (cs : List F) (hcap : cs.length < 2^26) (O : Opening) (c : F)
    (hValid : O.Valid c (foldAppend cs initTree).root) :
    leafAt cs O.index.val = c ∨ PathCollision cs O c := by
  have hRoot : (foldAppend cs initTree).root = treeHash cs 26 0 := (foldAppend_spec cs hcap).2.1
  have hCanon : (canonicalOpening cs O.index).calcRoot (leafAt cs O.index.val) = treeHash cs 26 0 :=
    calcRoot_canonicalOpening cs O.index
  -- Both `O` and the canonical opening of `O.index` fold to the same root; feed that to
  -- `telescope` to either extract the real leaf or exhibit the first colliding level.
  have hEq : foldUpTo (stepFn O.index.val (OpeningSib O)) 26 c
      = foldUpTo (stepFn O.index.val (OpeningSib (canonicalOpening cs O.index))) 26 (leafAt cs O.index.val) := by
    have e1 := calcRoot_eq_foldUpTo O c
    have e2 := calcRoot_eq_foldUpTo (canonicalOpening cs O.index) (leafAt cs O.index.val)
    rw [show (canonicalOpening cs O.index).index = O.index from rfl] at e2
    rw [← e1, ← e2]
    unfold Opening.Valid at hValid
    rw [hValid, hRoot, hCanon]
  rcases telescope O.index.val (OpeningSib O) (OpeningSib (canonicalOpening cs O.index)) c
      (leafAt cs O.index.val) 26 hEq with ⟨hL, _⟩ | ⟨h0, hh0, hcol⟩
  · exact Or.inl hL.symm
  · exact Or.inr (by unfold PathCollision; exact ⟨⟨h0, hh0⟩, hcol⟩)

-- LEMMA (used by G3a): preservation. A written leaf `k` of `cs` keeps a valid opening at
-- index `k` after more leaves are appended.
lemma opening_forward_preservation
    (cs later : List F) (k : ℕ) (hk : k < cs.length) (c : F) (hc : cs[k]'hk = c)
    (hcap : (cs ++ later).length < 2^26) :
    ∃ O' : Opening, O'.index.val = k ∧ O'.Valid c (foldAppend (cs++later) initTree).root := by
  have hlen : (cs++later).length = cs.length + later.length := by simp
  have hklt : k < 2^26 := by omega
  refine ⟨canonicalOpening (cs++later) ⟨k, hklt⟩, rfl, ?_⟩
  have h1 := calcRoot_canonicalOpening (cs++later) ⟨k, hklt⟩
  have h2 : leafAt (cs++later) k = c := by
    rw [leafAt_append_left cs later k hk]
    unfold leafAt
    rw [dif_pos hk]
    exact hc
  have h3 := (foldAppend_spec (cs++later) hcap).2.1
  show (canonicalOpening (cs++later) ⟨k, hklt⟩).calcRoot c = (foldAppend (cs++later) initTree).root
  rw [← h2, h1, ← h3]


-- LEMMA (used by G5): one step changes neither the config nor the rent-exempt minimum.
lemma config_and_rent_exempt_min_step
  (oldWorld newWorld: World)
  (inputs: TxInputs)
  (h: transact inputs oldWorld newWorld)
  : newWorld.state.config = oldWorld.state.config
    ∧ newWorld.rentExemptMin = oldWorld.rentExemptMin := by
  obtain ⟨_, heff⟩ := h
  refine ⟨?_, ?_⟩
  · rw [heff.config]; unfold transactEffects transferEffects; split_ifs <;> rfl
  · rw [heff.rentExemptMin]; unfold transactEffects transferEffects; split_ifs <;> rfl

-- LEMMA (used by G5): the same over any number of steps.
lemma config_and_rent_exempt_min_constant
  (params : InitParams) (w: World)
  (h: ReachableWorld (initWorld params) w)
  : w.state.config = params.cfg ∧ w.rentExemptMin = params.rentExemptMin := by
  induction h with
  | noStep => exact ⟨rfl, rfl⟩
  | extend inputs _ transact_proof ih =>
    obtain ⟨ihc, ihr⟩ := ih
    obtain ⟨hc, hr⟩ := config_and_rent_exempt_min_step _ _ inputs transact_proof
    exact ⟨hc.trans ihc, hr.trans ihr⟩


-- HELPER: a zero input is trivially bounded, so the `≠ 0` hypothesis can be dropped.
lemma inAmt_val_bound (witness : Witness)
    (hInBound : ∀ i, witness.inAmt i ≠ 0 → (witness.inAmt i).val < 2^248) :
    ∀ i, (witness.inAmt i).val < 2^248 := by
  intro i
  by_cases h : witness.inAmt i = 0
  · rw [h, ZMod.val_zero]; exact Nat.two_pow_pos 248
  · exact hInBound i h

-- HELPER: an `F` equation between integers is an integer equation when their difference
-- is below `p`.
lemma zmod_eq_iff_int_eq (a b : ℤ) (hbound : |a - b| < (p:ℤ)) (heq : (a : F) = (b : F)) :
    a = b := by
  have hdvd : (p:ℤ) ∣ (a - b) := (ZMod.intCast_eq_intCast_iff_dvd_sub b a p).mp heq.symm
  have := Int.eq_zero_of_abs_lt_dvd hdvd hbound
  omega

-- LEMMA (used by G1c): one step, in ℤ: output value − input value = extAmt − f. Lifts
-- `amountConservation` from `F`; needs every amount below `2^248`, so nothing wraps mod `p`.
lemma value_delta_eq_ext_sub_fee
    (witness : Witness) (pubInputs : PubInputs) (extAmt : ℤ) (f : ℕ)
    (hAC : witness.inAmt 0 + witness.inAmt 1 + pubInputs.pubAmt = witness.outAmt 0 + witness.outAmt 1)
    (hOR : ∀ j, (witness.outAmt j).val < 2^248)
    (hPubAmt : pubAmtConsistent extAmt f pubInputs.pubAmt)
    (hInBound : ∀ i, witness.inAmt i ≠ 0 → (witness.inAmt i).val < 2^248)
    (hExtBound : extAmt.natAbs < 2^248) (hFeeBound : f < 2^248) :
    ((witness.outAmt 0).val : ℤ) + (witness.outAmt 1).val
      - (witness.inAmt 0).val - (witness.inAmt 1).val = extAmt - f := by
  have hInVal := inAmt_val_bound witness hInBound
  have hi0 := hInVal 0
  have hi1 := hInVal 1
  have ho0 := hOR 0
  have ho1 := hOR 1
  -- The `F`-level identity this whole lemma is really about: rearranging
  -- `amountConservation` with `pubAmt = extAmt - f` substituted in.
  have hFeq : witness.inAmt 0 + witness.inAmt 1 + (extAmt : F)
      = witness.outAmt 0 + witness.outAmt 1 + (f : F) := by
    have hAC' := hAC
    rw [hPubAmt.2] at hAC'
    linear_combination hAC'
  -- Lift both sides to their `ℤ` counterparts via `.val`, then to `F` again to match `hFeq`.
  set L : ℤ := (witness.inAmt 0).val + (witness.inAmt 1).val + extAmt with hLdef
  set R : ℤ := (witness.outAmt 0).val + (witness.outAmt 1).val + (f : ℤ) with hRdef
  have hLF : (L : F) = witness.inAmt 0 + witness.inAmt 1 + (extAmt : F) := by
    rw [hLdef]; push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hRF : (R : F) = witness.outAmt 0 + witness.outAmt 1 + (f : F) := by
    rw [hRdef]; push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
  have hLReq : (L : F) = (R : F) := by rw [hLF, hRF]; exact hFeq
  -- Both sides are far below `p` (~2^254), so the `F` equation is a `ℤ` equation.
  have hp_lt : (2:ℤ)^250 < (p:ℤ) := by norm_num [p]
  have hbound : |L - R| < (p:ℤ) := by
    rw [abs_lt]
    constructor <;> [skip; skip] <;>
      · have := hp_lt
        omega
  have hLR := zmod_eq_iff_int_eq L R hbound hLReq
  rw [hLdef, hRdef] at hLR
  omega


/-- HELPER: `transact` completeness. If every check of `transact` except the proof holds, and every
    non-zero input is a leaf of `cs0` (with `later` appended since), Groth16 completeness gives a
    proof that makes `transact` succeed. The openings are rebuilt from the tree (`opening_forward_preservation`). -/
lemma transact_complete (hCompl : Groth16Complete)
  (oldWorld: World) (inputs: TxInputs) (witness: Witness)
  (cs0 later : List F) (hcap : (cs0 ++ later).length < 2^26)
  (hR : inputs.R = (foldAppend (cs0 ++ later) initTree).root)
  (hDeposited : ∀ i, witness.inAmt i ≠ 0 →
      (witness.openings i).index.val < cs0.length
      ∧ leafAt cs0 (witness.openings i).index.val = witness.inC i)
  (hOutputCommitmentIntegrity : ∀ j, inputs.pubInputs.outCommitments j
      = commit (witness.outAmt j) (witness.outPk j) (witness.outR j) witness.mint)
  (hNullifierCorrectness : ∀ i, inputs.pubInputs.nullifiers i
      = nullifier (witness.inC i) (witness.sign i) (witness.openings i).index)
  (hNoDuplicateNullifiers : inputs.pubInputs.nullifiers 0 ≠ inputs.pubInputs.nullifiers 1)
  (hAmountConservation : witness.inAmt 0 + witness.inAmt 1 + inputs.pubInputs.pubAmt
      = witness.outAmt 0 + witness.outAmt 1)
  (hOutputRangeChecks : ∀ j, (witness.outAmt j).val < 2^248)
  (hRoot: rootKnown oldWorld.state.tree inputs.R)
  (hData: externalDataBound inputs)
  (hFee: feeSufficient oldWorld.state.config inputs.extAmt inputs.f)
  (hPubAmt: pubAmtConsistent inputs.extAmt inputs.f inputs.pubAmt)
  (hFresh: nullifiersFresh oldWorld.state.nullifiers inputs.k0 inputs.k1)
  (hDistinct: nullifiersDistinct inputs.k0 inputs.k1)
  (hDeposit: depositWithinLimit oldWorld.state.config inputs.extAmt)
  (hSolvent: poolSolvent oldWorld.poolBalance oldWorld.rentExemptMin inputs.extAmt inputs.f)
  (hSignerSolvent: signerSolvent oldWorld.balances inputs.s inputs.extAmt oldWorld.nullifierRent)
  (hRoom: treeHasRoom oldWorld.state.tree)
  (hRange: amountsInRange inputs.extAmt inputs.f)
  (hEnc: encOutsFit inputs)
  (hSep: poolIsSeparate inputs oldWorld.state.pool)
  : ∃ π, transact { inputs with π := π } oldWorld (transactEffects { inputs with π := π } oldWorld) := by
  classical
  -- For each spent input, use `opening_forward_preservation` to get a genuinely valid opening at the
  -- same claimed index, against the *current* root `inputs.R` (not just `cs0`'s).
  have hOpen : ∀ i : Fin 2, witness.inAmt i ≠ 0 → ∃ O' : Opening,
      O'.index = (witness.openings i).index ∧ O'.Valid (witness.inC i) inputs.R := by
    intro i hne
    obtain ⟨hlt, heq⟩ := hDeposited i hne
    have hc : cs0[(witness.openings i).index.val]'hlt = witness.inC i := by
      have hh := heq
      unfold leafAt at hh
      rwa [dif_pos hlt] at hh
    obtain ⟨O', hidx, hvalid⟩ :=
      opening_forward_preservation cs0 later (witness.openings i).index.val hlt (witness.inC i) hc hcap
    exact ⟨O', Fin.ext hidx, by rw [hR]; exact hvalid⟩
  -- `witness'`: `witness` with each non-zero input's opening replaced by the one just
  -- derived -- same claimed index, so everything computed from the index (nullifier,
  -- signature) is unaffected; only the siblings, previously a bare hypothesis, change.
  set witness' : Witness := { witness with
    openings := fun i => if h : witness.inAmt i ≠ 0 then Classical.choose (hOpen i h) else witness.openings i
  } with hwitness'_def
  have hIdxEq : ∀ i, (witness'.openings i).index = (witness.openings i).index := by
    intro i
    by_cases h : witness.inAmt i ≠ 0
    · show (if h' : witness.inAmt i ≠ 0 then Classical.choose (hOpen i h') else witness.openings i).index
        = (witness.openings i).index
      rw [dif_pos h]
      exact (Classical.choose_spec (hOpen i h)).1
    · show (if h' : witness.inAmt i ≠ 0 then Classical.choose (hOpen i h') else witness.openings i).index
        = (witness.openings i).index
      rw [dif_neg h]
  have hSignEq : ∀ i, witness'.sign i = witness.sign i := by
    intro i
    show signature (witness.inSk i) (witness.inC i) (witness'.openings i).index
       = signature (witness.inSk i) (witness.inC i) (witness.openings i).index
    rw [hIdxEq]
  have hRel' : RelationS inputs.pubInputs witness' := {
    outputCommitmentIntegrity := hOutputCommitmentIntegrity
    nullifierCorrectness := fun i => by
      show inputs.pubInputs.nullifiers i
        = nullifier (witness.inC i) (witness'.sign i) (witness'.openings i).index
      rw [hSignEq, hIdxEq]
      exact hNullifierCorrectness i
    noDuplicateNullifiers := hNoDuplicateNullifiers
    correctOpenings := fun i hne => by
      have hne' : witness.inAmt i ≠ 0 := hne
      show (witness'.openings i).Valid (witness.inC i) inputs.R
      show (if h' : witness.inAmt i ≠ 0 then Classical.choose (hOpen i h') else witness.openings i).Valid
        (witness.inC i) inputs.R
      rw [dif_pos hne']
      exact (Classical.choose_spec (hOpen i hne')).2
    amountConservation := hAmountConservation
    outputRangeChecks := hOutputRangeChecks
  }
  obtain ⟨π, hπ⟩ := hCompl inputs.pubInputs witness' hRel'
  refine ⟨π, ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩
  exact {
    knownRoot := hRoot
    externalDataBinding := hData
    minimumFee := hFee
    pubAmtConsistency := hPubAmt
    validZKP := hπ
    newNullifiers := hFresh
    distinctNullifiers := hDistinct
    signerSolvency := hSignerSolvent
    depositLimit := hDeposit
    poolSolvency := hSolvent
    treeNotFull := hRoom
    amountRange := hRange
    encOutLength := hEnc
    poolSeparate := hSep
  }

-- LEMMA (used by every theorem about a run): each transaction of a run is accepted, so its
-- proof verifies (`validZKP`), so `wit` gives a witness for it. This is where the proof check
-- enters the theorems.
lemma Run.WitnessesFor.relation {w0 : World} {r : Run w0} {wit : ℕ → Witness}
    (hwit : r.WitnessesFor wit) (j : ℕ) (hj : j < r.txs.length) :
    RelationS r.txs[j].pubInputs (wit j) :=
  hwit j hj (r.step j hj).1.validZKP

-- LEMMAS (not for review) about `leaves`.

lemma leaves_append (a b : List TxInputs) : leaves (a ++ b) = leaves a ++ leaves b := by
  simp [leaves, List.flatMap_append]

lemma leaves_length (txs : List TxInputs) : (leaves txs).length = 2 * txs.length := by
  induction txs with
  | nil => rfl
  | cons tx rest ih =>
    simp only [leaves, List.flatMap_cons, List.length_append, List.length_cons,
      List.length_nil] at ih ⊢
    omega

lemma leafAt_cons_cons (a b : F) (L : List F) (n : ℕ) :
    leafAt (a :: b :: L) (n + 2) = leafAt L n := by
  unfold leafAt
  by_cases h : n < L.length
  · rw [dif_pos (by simp; omega), dif_pos h]; simp
  · rw [dif_neg (by simp; omega), dif_neg h]

lemma leafAt_take (cs : List F) (k pos : ℕ) (h : pos < k) : leafAt (cs.take k) pos = leafAt cs pos := by
  unfold leafAt
  by_cases hpos : pos < cs.length
  · rw [dif_pos (by simp; omega), dif_pos hpos]; simp
  · rw [dif_neg (by simp; omega), dif_neg hpos]

/-- Leaf `2m + o` is output `o` of transaction `m`. -/
lemma leafAt_leaves (txs : List TxInputs) (m : ℕ) (hm : m < txs.length) (o : Fin 2) :
    leafAt (leaves txs) (2 * m + o.val) = txs[m].pubInputs.outCommitments o := by
  induction txs generalizing m with
  | nil => simp at hm
  | cons tx rest ih =>
    cases m with
    | zero =>
      fin_cases o <;> simp [leaves, leafAt, TxInputs.pubInputs]
    | succ m =>
      have : 2 * (m + 1) + o.val = (2 * m + o.val) + 2 := by omega
      rw [this]
      simp only [leaves, List.flatMap_cons, List.cons_append, List.nil_append]
      rw [leafAt_cons_cons]
      exact ih m (by simp at hm; omega)

-- LEMMAS (not for review) about runs.

lemma Run.take_succ {w0 : World} (r : Run w0) (j : ℕ) (hj : j < r.txs.length) :
    r.txs.take (j+1) = r.txs.take j ++ [r.txs[j]] := by
  exact List.take_succ_eq_append_getElem hj

lemma Run.leaves_take_succ {w0 : World} (r : Run w0) (j : ℕ) (hj : j < r.txs.length) :
    leaves (r.txs.take (j+1)) = leaves (r.txs.take j) ++ [r.txs[j].outC0, r.txs[j].outC1] := by
  rw [r.take_succ j hj, leaves_append]; simp [leaves]

lemma Run.leaves_take_length {w0 : World} (r : Run w0) (j : ℕ) (hj : j ≤ r.txs.length) :
    (leaves (r.txs.take j)).length = 2 * j := by
  rw [leaves_length, List.length_take]; omega

/-- Each world of a run is reachable from the start. -/
lemma Run.reachable {w0 : World} (r : Run w0) :
    ∀ j ≤ r.txs.length, ReachableWorld w0 (r.ws j) := by
  intro j
  induction j with
  | zero => intro _; rw [r.start]; exact ReachableWorld.noStep _
  | succ j ih => intro hj; exact ReachableWorld.extend _ (ih (by omega)) (r.step j (by omega))

/-- Every reachable world is the final world of some run. -/
lemma ReachableWorld.exists_run {w0 w : World} (h : ReachableWorld w0 w) :
    ∃ r : Run w0, r.final = w := by
  induction h with
  | noStep => exact ⟨⟨[], fun _ => _, rfl, fun j h => absurd h (by simp)⟩, rfl⟩
  | @extend w2 w3 tx _ htx ih =>
    obtain ⟨r, hr⟩ := ih
    refine ⟨⟨r.txs ++ [tx], fun j => if j ≤ r.txs.length then r.ws j else w3, ?_, ?_⟩, ?_⟩
    · simp [r.start]
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      by_cases hjn : j < r.txs.length
      · rw [List.getElem_append_left hjn, if_pos (by omega), if_pos (by omega)]
        exact r.step j hjn
      · have hjeq : j = r.txs.length := by omega
        subst hjeq
        rw [List.getElem_append_right (by omega), if_pos le_rfl, if_neg (by omega)]
        simp only [Nat.sub_self, List.getElem_singleton]
        rw [← hr] at htx; exact htx
    · simp [Run.final]

/-- The tree of world `j` holds exactly the leaves of the first `j` transactions, and every
    root in its history is `0` (an untouched slot) or the root of a prefix of those leaves. -/
lemma Run.tree {params : InitParams}
    (r : Run (initWorld params)) :
    ∀ j ≤ r.txs.length,
      (r.ws j).state.tree = foldAppend (leaves (r.txs.take j)) initTree ∧
      ∀ R ∈ Set.range (r.ws j).state.tree.history,
        R = 0 ∨ ∃ k ≤ 2 * j, R = (foldAppend ((leaves (r.txs.take j)).take k) initTree).root := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [r.start]
    refine ⟨by simp [leaves, foldAppend, initWorld], ?_⟩
    intro R hR
    obtain ⟨i, hi⟩ := hR
    simp only [initWorld, initTree] at hi
    split_ifs at hi
    · exact Or.inr ⟨0, le_rfl, by simp [leaves, foldAppend, initTree]; exact hi.symm⟩
    · exact Or.inl hi.symm
  | succ j ih =>
    intro hj
    have hjn : j < r.txs.length := by omega
    obtain ⟨hcs, hhist⟩ := ih (by omega)
    obtain ⟨_, hagree⟩ := r.step j hjn
    have hlen := r.leaves_take_length j (by omega)
    set cs := leaves (r.txs.take j) with hcs_def
    have hnew := r.leaves_take_succ j hjn
    rw [← hcs_def] at hnew
    rw [hnew]
    have hfold : ∀ ys : List F,
        foldAppend (cs ++ ys) initTree = foldAppend ys (foldAppend cs initTree) := by
      intro ys; simp [foldAppend, List.foldl_append]
    refine ⟨?_, ?_⟩
    · rw [hagree.tree, hfold, ← hcs]
      simp only [transactEffects, transferEffects_tree, nullifierRentEffects_state, foldAppend, List.foldl_cons,
        List.foldl_nil]
    · intro R hR
      rw [hagree.tree] at hR
      simp only [transactEffects, transferEffects_tree, nullifierRentEffects_state] at hR
      rw [appendEffects_history] at hR
      rcases mem_range_update_or_mem_range _ _ _ _ hR with hEq | hR'
      · -- root after both outputs: all of the new leaves
        refine Or.inr ⟨cs.length + 2, by omega, ?_⟩
        rw [List.take_of_length_le (by simp), hfold, ← hcs]
        exact hEq
      rw [appendEffects_history] at hR'
      rcases mem_range_update_or_mem_range _ _ _ _ hR' with hEq | hR''
      · -- root after `outC0` only
        refine Or.inr ⟨cs.length + 1, by omega, ?_⟩
        rw [show (cs ++ [r.txs[j].outC0, r.txs[j].outC1]).take (cs.length + 1)
            = cs ++ [r.txs[j].outC0] by rw [List.take_append]; simp, hfold, ← hcs]
        exact hEq
      · rcases hhist R hR'' with h0 | ⟨k, hk, hRk⟩
        · exact Or.inl h0
        · refine Or.inr ⟨k, by omega, ?_⟩
          rw [List.take_append_of_le_length (by omega)]
          exact hRk

/-- Before each transaction the tree has room for its two outputs (`treeNotFull`). -/
lemma Run.cap {params : InitParams}
    (r : Run (initWorld params)) (j : ℕ) (hj : j < r.txs.length) :
    2 * j ≤ 2^26 - 2 := by
  have hroom := (r.step j hj).1.treeNotFull
  unfold treeHasRoom at hroom
  rw [(r.tree j hj.le).1, foldAppend_nextIndex, r.leaves_take_length j hj.le] at hroom
  exact hroom

lemma Run.final_cap {params : InitParams}
    (r : Run (initWorld params)) : 2 * r.txs.length ≤ 2^26 := by
  rcases Nat.eq_zero_or_pos r.txs.length with h0 | hpos
  · rw [h0]; norm_num
  · have := r.cap (r.txs.length - 1) (by omega); omega

/-- The final tree holds the run's `2 · txs.length` leaves. -/
lemma Run.final_nextIndex {params : InitParams} (r : Run (initWorld params)) :
    r.final.state.tree.nextIndex = 2 * r.txs.length := by
  have h := (r.tree r.txs.length le_rfl).1
  rw [show r.final = r.ws r.txs.length from rfl, h, foldAppend_nextIndex, r.leaves_take_length _ le_rfl]

/-- The current root of a `foldAppend` tree is in its history. -/
lemma foldAppend_root_mem_history (cs : List F) :
    (foldAppend cs initTree).root ∈ Set.range (foldAppend cs initTree).history := by
  refine ⟨(foldAppend cs initTree).rootIndex, ?_⟩
  induction cs using List.reverseRecOn with
  | nil => rfl
  | append_singleton ys y _ =>
    have : foldAppend (ys ++ [y]) initTree = appendEffects y (foldAppend ys initTree) := by
      simp [foldAppend]
    rw [this, appendEffects_history]
    exact Function.update_self _ _ _

/-- A nullifier spent by transaction `j` is in the nullifier set of every later world. -/
lemma Run.nullifier_spent {w0 : World} (r : Run w0) (j : ℕ) (hj : j < r.txs.length) (i : Fin 2) :
    ∀ j', j < j' → j' ≤ r.txs.length → r.txs[j].pubInputs.nullifiers i ∈ (r.ws j').state.nullifiers := by
  intro j' hjj'
  induction j' with
  | zero => omega
  | succ j' ih =>
    intro hj'
    by_cases hlt : j < j'
    · exact (nullifier_set_monotonicity_step _ _ _ (r.step j' (by omega))).subset (ih hlt (by omega))
    · have hjeq : j = j' := by omega
      subst hjeq
      obtain ⟨_, hagree⟩ := r.step j hj
      rw [hagree.nullifiers]
      simp only [transactEffects, transferEffects]
      fin_cases i <;> split_ifs <;> simp [TxInputs.pubInputs]

/-- A nullifier spent by transaction `j` was not in the nullifier set before it. -/
lemma Run.nullifier_fresh {w0 : World} (r : Run w0) (j : ℕ) (hj : j < r.txs.length) (i : Fin 2) :
    r.txs[j].pubInputs.nullifiers i ∉ (r.ws j).state.nullifiers := by
  have hfresh := (r.step j hj).1.newNullifiers
  fin_cases i
  · exact hfresh.1
  · exact hfresh.2

/-- The pool's SOL after the first `j` transactions: rent reserve plus their `extAmt − f`. -/
lemma Run.poolBalance {params : InitParams}
    (r : Run (initWorld params)) :
    ∀ j ≤ r.txs.length, ((r.ws j).poolBalance : ℤ)
      = params.rentExemptMin + ((r.txs.take j).map (fun tx => tx.extAmt - (tx.f : ℤ))).sum := by
  intro j
  induction j with
  | zero => intro _; rw [r.start]; simp [initWorld, World.poolBalance]
  | succ j ih =>
    intro hj
    rw [sol_balance_correctness_step _ _ _ (r.step j (by omega)), ih (by omega),
      r.take_succ j (by omega)]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
      List.sum_nil]
    ring

--/////////////////////////////////////////
-- Proofs of the theorems. Their statements and explanations: `Spec/Statements.lean`.
--/////////////////////////////////////////

/-! ## G1. Balance -/

-- PROOF of G1a. Statement and explanation: `Spec/Statements.lean`.
theorem spends_are_genuine
    (params : InitParams)
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)
    (j : ℕ) (hj : j < r.txs.length) (i : Fin 2) (hne : (wit j).inAmt i ≠ 0) :
    (spentLeaf wit j i < 2 * j ∧ (wit j).inNote i = leafNote wit (spentLeaf wit j i))
    ∨ SpendBreak r wit j i := by
  obtain ⟨hpre, _⟩ := r.step j hj
  have hRel := hwit.relation j hj
  obtain ⟨_, hhist⟩ := r.tree j hj.le
  obtain ⟨hRmem, hR0⟩ := hpre.knownRoot
  have hlen := r.leaves_take_length j hj.le
  have hcap := r.cap j hj
  rcases hhist _ hRmem with h0 | ⟨k, hk, hRk⟩
  · exact absurd h0 hR0
  set cs := leaves (r.txs.take j) with hcs_def
  have hValid : ((wit j).openings i).Valid ((wit j).inC i) (foldAppend (cs.take k) initTree).root := by
    rw [← hRk]; exact hRel.correctOpenings i hne
  have hklen : (cs.take k).length = k := by rw [List.length_take]; omega
  rcases opening_extractable_or_collision (cs.take k) (by omega) _ _ hValid with hleaf | hcol
  · by_cases hposk : spentLeaf wit j i < k
    · have hm : spentLeaf wit j i / 2 < r.txs.length := by omega
      have hleaf' : leafAt (leaves r.txs) (spentLeaf wit j i) = (wit j).inC i := by
        have hsplit : leaves r.txs = cs ++ leaves (r.txs.drop j) := by
          rw [hcs_def, ← leaves_append, List.take_append_drop]
        rw [hsplit, leafAt_append_left _ _ _ (by omega), ← leafAt_take _ _ _ hposk]
        exact hleaf
      have hpos : spentLeaf wit j i = 2 * (spentLeaf wit j i / 2)
          + (⟨spentLeaf wit j i % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2).val := by
        simp only; omega
      rw [hpos, leafAt_leaves _ _ hm, (hwit.relation _ hm).outputCommitmentIntegrity] at hleaf'
      rcases commitment_determines_value_or_collision _ _ _ _ _ _ _ _ hleaf'.symm with heq | hcoll
      · exact Or.inl ⟨by omega, heq⟩
      · exact Or.inr (Or.inr (Or.inr hcoll))
    · refine Or.inr (Or.inr (Or.inl ⟨?_⟩))
      have hz : leafAt (cs.take k) (spentLeaf wit j i) = 0 := by
        unfold leafAt; rw [dif_neg (by omega)]; rfl
      unfold spentLeaf at hz
      rw [hz] at hleaf
      exact hleaf.symm
  · exact Or.inr (Or.inl ⟨k, hk, hcol⟩)

-- PROOF of G1b. Statement and explanation: `Spec/Statements.lean`.
theorem no_double_spend
    (params : InitParams)
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)
    (j j' : ℕ) (hj : j < r.txs.length) (hj' : j' < r.txs.length) (i i' : Fin 2)
    (hne : (wit j).inAmt i ≠ 0) (hne' : (wit j').inAmt i' ≠ 0)
    (hdiff : (j, i) ≠ (j', i')) (hsame : spentLeaf wit j i = spentLeaf wit j' i') :
    SpendBreak r wit j i ∨ SpendBreak r wit j' i'
      ∨ H1Collision ((wit j).inSk i) ((wit j').inSk i') := by
  rcases spends_are_genuine params r wit hwit j hj i hne with ⟨_, hn⟩ | hb
  swap; · exact Or.inl hb
  rcases spends_are_genuine params r wit hwit j' hj' i' hne' with ⟨_, hn'⟩ | hb'
  swap; · exact Or.inr (Or.inl hb')
  right; right
  have hnote : (wit j).inNote i = (wit j').inNote i' := by rw [hn, hn', hsame]
  have hC : (wit j).inC i = (wit j').inC i' := by
    simp only [Witness.inNote, Note.mk.injEq] at hnote
    obtain ⟨h1, h2, h3, h4⟩ := hnote
    simp only [Witness.inC, commit]; rw [h1, h2, h3, h4]
  have hIdx : ((wit j).openings i).index = ((wit j').openings i').index := Fin.ext hsame
  rcases same_commitment_same_nullifier_or_collision (wit j) (wit j') _ _ (hwit.relation j hj) (hwit.relation j' hj')
      i i' hIdx hC with hN | hH1 | hH4
  · exfalso
    rcases lt_trichotomy j j' with hlt | heq | hgt
    · have hin := r.nullifier_spent j hj i j' hlt hj'.le
      rw [hN] at hin
      exact r.nullifier_fresh j' hj' i' hin
    · subst heq
      have hii : i ≠ i' := fun h => hdiff (by rw [h])
      have hnd := (hwit.relation j hj).noDuplicateNullifiers
      fin_cases i <;> fin_cases i'
      · exact hii rfl
      · exact hnd hN
      · exact hnd hN.symm
      · exact hii rfl
    · have hin := r.nullifier_spent j' hj' i' j hgt hj.le
      rw [← hN] at hin
      exact r.nullifier_fresh j hj i hin
  · exact hH1
  · exact absurd hnote hH4.ne

-- PROOF of G1c. Statement and explanation: `Spec/Statements.lean`.
theorem balance
    (params : InitParams)
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit) :
    (r.final.poolBalance : ℤ) = params.rentExemptMin + ∑ pos ∈ r.unspent wit, leafValue wit pos
    ∨ BalanceBreak r wit := by
  classical
  have hBound : ∀ j (h : j < r.txs.length), r.txs[j].extAmt.natAbs < 2^248 ∧ r.txs[j].f < 2^248 := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := (r.step j hj).1.amountRange
    constructor <;> omega
  by_cases hB1 : ∃ j < r.txs.length, ∃ i, (wit j).inAmt i ≠ 0 ∧ SpendBreak r wit j i
  · exact Or.inr (by unfold BalanceBreak; exact Or.inl hB1)
  by_cases hB2 : ∃ j < r.txs.length, ∃ j' < r.txs.length, ∃ i i', (wit j).inAmt i ≠ 0
      ∧ (wit j').inAmt i' ≠ 0 ∧ (j, i) ≠ (j', i') ∧ spentLeaf wit j i = spentLeaf wit j' i'
      ∧ H1Collision ((wit j).inSk i) ((wit j').inSk i')
  · exact Or.inr (by unfold BalanceBreak; exact Or.inr hB2)
  left
  -- With no breaks, G1a and G1b hold outright.
  have hgen : ∀ j (hj : j < r.txs.length) i, (wit j).inAmt i ≠ 0 →
      spentLeaf wit j i < 2 * j ∧ (wit j).inNote i = leafNote wit (spentLeaf wit j i) := by
    intro j hj i hne
    rcases spends_are_genuine params r wit hwit j hj i hne with h | h
    · exact h
    · exact absurd ⟨j, hj, i, hne, h⟩ hB1
  have hinj : ∀ j (hj : j < r.txs.length) j' (hj' : j' < r.txs.length) i i',
      (wit j).inAmt i ≠ 0 → (wit j').inAmt i' ≠ 0 →
      spentLeaf wit j i = spentLeaf wit j' i' → (j, i) = (j', i') := by
    intro j hj j' hj' i i' hne hne' hsame
    by_contra hdiff
    rcases no_double_spend params r wit hwit j j' hj hj' i i' hne hne' hdiff
        hsame with h | h | h
    · exact hB1 ⟨j, hj, i, hne, h⟩
    · exact hB1 ⟨j', hj', i', hne', h⟩
    · exact hB2 ⟨j, hj, j', hj', i, i', hne, hne', hdiff, hsame, h⟩
  -- Each spent amount is the value of the note it opens, hence below 2^248.
  have hinval : ∀ j (hj : j < r.txs.length) i, (wit j).inAmt i ≠ 0 →
      (((wit j).inAmt i).val : ℤ) = leafValue wit (spentLeaf wit j i)
      ∧ ((wit j).inAmt i).val < 2^248 := by
    intro j hj i hne
    obtain ⟨hlt, hnote⟩ := hgen j hj i hne
    have hamt : (wit j).inAmt i = (leafNote wit (spentLeaf wit j i)).amount := congrArg Note.amount hnote
    refine ⟨by rw [hamt]; rfl, ?_⟩
    rw [hamt]
    exact (hwit.relation (spentLeaf wit j i / 2) (by omega)).outputRangeChecks _
  set inV : ℕ → Fin 2 → ℤ := fun x i => (((wit x).inAmt i).val : ℤ) with hinV
  -- After `j` transactions: pool = rent + value created − value spent.
  have hA : ∀ j ≤ r.txs.length, ((r.ws j).poolBalance : ℤ)
      = params.rentExemptMin + ∑ pos ∈ Finset.range (2 * j), leafValue wit pos
        - ∑ x ∈ Finset.range j, (inV x 0 + inV x 1) := by
    intro j
    induction j with
    | zero => intro _; rw [r.start]; simp [initWorld, World.poolBalance]
    | succ j ih =>
      intro hj
      have hjn : j < r.txs.length := by omega
      have hstep := sol_balance_correctness_step _ _ _ (r.step j hjn)
      have hbd := hBound j hjn
      have hdelta := value_delta_eq_ext_sub_fee (wit j) r.txs[j].pubInputs r.txs[j].extAmt
        r.txs[j].f (hwit.relation j hjn).amountConservation (hwit.relation j hjn).outputRangeChecks
        (r.step j hjn).1.pubAmtConsistency
        (fun i hne => (hinval j hjn i hne).2) hbd.1 hbd.2
      have hl0 : leafValue wit (2 * j) = (((wit j).outAmt 0).val : ℤ) := by
        unfold leafValue leafNote Witness.outNote
        have e : 2 * j / 2 = j := by omega
        have hf : (⟨2 * j % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 0 := Fin.ext (by simp)
        rw [hf, e]
      have hl1 : leafValue wit (2 * j + 1) = (((wit j).outAmt 1).val : ℤ) := by
        unfold leafValue leafNote Witness.outNote
        have e : (2 * j + 1) / 2 = j := by omega
        have hf : (⟨(2 * j + 1) % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2) = 1 := Fin.ext (by simp)
        rw [hf, e]
      rw [show 2 * (j+1) = 2 * j + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, hstep, ih (by omega), hl0, hl1]
      simp only [hinV]
      linarith
  -- The spent leaves, and the spent value as a sum over them.
  set S : Finset (ℕ × Fin 2) :=
    (Finset.range r.txs.length ×ˢ Finset.univ).filter (fun p => (wit p.1).inAmt p.2 ≠ 0) with hS
  set g : ℕ × Fin 2 → ℕ := fun p => spentLeaf wit p.1 p.2 with hg
  have hB : ∑ x ∈ Finset.range r.txs.length, (inV x 0 + inV x 1) = ∑ pos ∈ S.image g, leafValue wit pos := by
    rw [Finset.sum_image]
    · rw [hS, Finset.sum_filter, Finset.sum_product]
      apply Finset.sum_congr rfl
      intro x hx
      have hxn : x < r.txs.length := Finset.mem_range.mp hx
      rw [Fin.sum_univ_two]
      congr 1
      · split_ifs with h
        · exact (hinval x hxn 0 h).1
        · simp only [hinV]; rw [not_not.mp h]; simp
      · split_ifs with h
        · exact (hinval x hxn 1 h).1
        · simp only [hinV]; rw [not_not.mp h]; simp
    · intro p hp q hq hpq
      simp only [hS, Finset.coe_filter, Finset.mem_product, Finset.mem_range, Finset.mem_univ,
        and_true, Set.mem_setOf_eq] at hp hq
      have := hinj p.1 hp.1 q.1 hq.1 p.2 q.2 hp.2 hq.2 hpq
      exact Prod.ext (congrArg Prod.fst this) (congrArg Prod.snd this)
  have hsub : S.image g ⊆ Finset.range (2 * r.txs.length) := by
    intro pos hpos
    simp only [Finset.mem_image, hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true] at hpos
    obtain ⟨⟨x, i⟩, ⟨hx, hne⟩, rfl⟩ := hpos
    have := (hgen x hx i hne).1
    simp only [Finset.mem_range, hg]; omega
  have hunspent : r.unspent wit = (Finset.range (2 * r.txs.length)).filter (fun pos => pos ∉ S.image g) := by
    unfold Run.unspent
    apply Finset.filter_congr
    intro pos _
    simp only [Finset.mem_image, hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
      Finset.mem_univ, and_true, hg, Prod.exists]
    constructor
    · rintro h ⟨a, b, ⟨ha, hb⟩, hab⟩; exact h ⟨a, ha, b, hb, hab⟩
    · rintro h ⟨a, ha, b, hb, hab⟩; exact h ⟨a, b, ⟨ha, hb⟩, hab⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.range (2 * r.txs.length))
    (fun pos => pos ∈ S.image g) (leafValue wit)
  rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hsub] at hsplit
  have hfin := hA r.txs.length le_rfl
  rw [hB] at hfin
  rw [hunspent]
  show ((r.ws r.txs.length).poolBalance : ℤ) = _
  linarith

-- PROOF of G1d. Statement and explanation: `Spec/Statements.lean`.
theorem honest_note_spent_only_with_owner_key
    (params : InitParams)
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)
    (j : ℕ) (hj : j < r.txs.length) (i : Fin 2) (hne : (wit j).inAmt i ≠ 0)
    (skOwner : F) (hOwner : (leafNote wit (spentLeaf wit j i)).ownerPk = H1 skOwner) :
    (wit j).inSk i = skOwner ∨ SpendBreak r wit j i ∨ H1Collision skOwner ((wit j).inSk i) := by
  rcases spends_are_genuine params r wit hwit j hj i hne
      with ⟨_, hnote⟩ | hb
  · have hpk : H1 ((wit j).inSk i) = H1 skOwner := by
      have := congrArg Note.ownerPk hnote
      simp only [Witness.inNote, Witness.inPk] at this
      rw [this, hOwner]
    by_cases hsk : (wit j).inSk i = skOwner
    · exact Or.inl hsk
    · exact Or.inr (Or.inr ⟨Ne.symm hsk, hpk.symm⟩)
  · exact Or.inr (Or.inl hb)

-- PROOF of G1e. Statement and explanation: `Spec/Statements.lean`.
theorem transact_requires_valid_proof
    (oldWorld newWorld : World) (inputs : TxInputs) (h : ¬ proofValid inputs) :
    ¬ transact inputs oldWorld newWorld :=
  fun ht => h ht.1.validZKP

/-! ## G2. Non-malleability -/

-- LEMMAS (used by G2a): the Borsh encoding of the external data is injective on in-range
-- values, so equal bytes mean equal fields.

lemma natToBytesLE_succ (w n : ℕ) :
    natToBytesLE (w+1) n = BitVec.ofNat 8 n :: natToBytesLE w (n >>> 8) := by
  unfold natToBytesLE
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp]
  rw [← Nat.shiftRight_add]
  congr 2; simp only [Nat.succ_eq_add_one]; ring

lemma natToBytesLE_length (w n : ℕ) : (natToBytesLE w n).length = w := by
  simp [natToBytesLE]

lemma natOfLE_natToBytesLE : ∀ (w n : ℕ), natOfLE (natToBytesLE w n) = n % 2^(8*w)
  | 0, n => by simp [natToBytesLE, natOfLE, Nat.mod_one]
  | w+1, n => by
    rw [natToBytesLE_succ]
    have ih := natOfLE_natToBytesLE w (n >>> 8)
    simp only [natOfLE, List.foldr_cons] at ih ⊢
    rw [ih, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [show 8 * (w+1) = 8 + 8 * w by ring, pow_add, Nat.mod_mul]
    norm_num

lemma natToBytesLE_inj (w n m : ℕ) (hn : n < 2^(8*w)) (hm : m < 2^(8*w))
    (h : natToBytesLE w n = natToBytesLE w m) : n = m := by
  have := congrArg natOfLE h
  rwa [natOfLE_natToBytesLE, natOfLE_natToBytesLE, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hm] at this

lemma PubkeyToBytes_inj (a b : Pubkey) (h : PubkeyToBytes a = PubkeyToBytes b) : a = b := by
  unfold PubkeyToBytes at h
  have ha := a.isLt; have hb := b.isLt
  exact BitVec.eq_of_toNat_eq (natToBytesLE_inj 32 _ _ (by norm_num at ha ⊢; omega)
    (by norm_num at hb ⊢; omega) h)

lemma u64LE_inj (n m : ℕ) (hn : n < 2^64) (hm : m < 2^64) (h : u64LE n = u64LE m) : n = m :=
  natToBytesLE_inj 8 n m (by norm_num at hn ⊢; omega) (by norm_num at hm ⊢; omega) h

lemma u32LE_inj (n m : ℕ) (hn : n < 2^32) (hm : m < 2^32) (h : u32LE n = u32LE m) : n = m :=
  natToBytesLE_inj 4 n m (by norm_num at hn ⊢; omega) (by norm_num at hm ⊢; omega) h

lemma i64LE_inj (x y : ℤ) (hx : -2^63 ≤ x ∧ x < 2^63) (hy : -2^63 ≤ y ∧ y < 2^63)
    (h : i64LE x = i64LE y) : x = y := by
  unfold i64LE at h
  have hx1 : 0 ≤ x % 2^64 := Int.emod_nonneg _ (by norm_num)
  have hx2 : x % 2^64 < 2^64 := Int.emod_lt_of_pos _ (by norm_num)
  have hy1 : 0 ≤ y % 2^64 := Int.emod_nonneg _ (by norm_num)
  have hy2 : y % 2^64 < 2^64 := Int.emod_lt_of_pos _ (by norm_num)
  have := natToBytesLE_inj 8 _ _ (by norm_num; omega) (by norm_num; omega) h
  omega

lemma serealizeExternalData_inj (T T' : TxInputs)
    (hT : amountsInRange T.extAmt T.f) (hT' : amountsInRange T'.extAmt T'.f)
    (h0 : T.encOut0.length < 2^32) (h1 : T.encOut1.length < 2^32)
    (h0' : T'.encOut0.length < 2^32) (h1' : T'.encOut1.length < 2^32)
    (h : serealizeExternalData T = serealizeExternalData T') :
    T.A = T'.A ∧ T.extAmt = T'.extAmt ∧ T.encOut0 = T'.encOut0 ∧ T.encOut1 = T'.encOut1
      ∧ T.f = T'.f ∧ T.t = T'.t ∧ T.mintAddr = T'.mintAddr := by
  unfold serealizeExternalData vecU8 at h
  simp only [List.append_assoc] at h
  obtain ⟨hA, h⟩ := List.append_inj h (by simp [PubkeyToBytes, natToBytesLE_length])
  obtain ⟨hE, h⟩ := List.append_inj h (by simp [i64LE, natToBytesLE_length])
  obtain ⟨hL0, h⟩ := List.append_inj h (by simp [u32LE, natToBytesLE_length])
  obtain ⟨hE0, h⟩ := List.append_inj h (u32LE_inj _ _ h0 h0' hL0)
  obtain ⟨hL1, h⟩ := List.append_inj h (by simp [u32LE, natToBytesLE_length])
  obtain ⟨hE1, h⟩ := List.append_inj h (u32LE_inj _ _ h1 h1' hL1)
  obtain ⟨hF, h⟩ := List.append_inj h (by simp [u64LE, natToBytesLE_length])
  obtain ⟨ht, hM⟩ := List.append_inj h (by simp [PubkeyToBytes, natToBytesLE_length])
  obtain ⟨r1, r2, r3⟩ := hT
  obtain ⟨r1', r2', r3'⟩ := hT'
  exact ⟨PubkeyToBytes_inj _ _ hA, i64LE_inj _ _ ⟨r1.le, r2⟩ ⟨r1'.le, r2'⟩ hE, hE0, hE1,
    u64LE_inj _ _ r3 r3' hF, PubkeyToBytes_inj _ _ ht, PubkeyToBytes_inj _ _ hM⟩

-- PROOF of G2a. Statement and explanation: `Spec/Statements.lean`.
theorem same_public_inputs_same_external_data
    (T T' : TxInputs) (oldWorld' newWorld' : World)
    -- `T`: the honest transaction, as observed (well formed)
    (hT : externalDataBound T ∧ amountsInRange T.extAmt T.f ∧ encOutsFit T)
    -- `T'`: the attacker's transaction, accepted by the program
    (h' : transact T' oldWorld' newWorld')
    (hSame : T.pubInputs = T'.pubInputs) :
    (T.A = T'.A ∧ T.extAmt = T'.extAmt ∧ T.encOut0 = T'.encOut0 ∧ T.encOut1 = T'.encOut1
      ∧ T.f = T'.f ∧ T.t = T'.t ∧ T.mintAddr = T'.mintAddr)
    ∨ Sha256Collision (serealizeExternalData T) (serealizeExternalData T') := by
  by_cases hser : serealizeExternalData T = serealizeExternalData T'
  · obtain ⟨l0, l1⟩ := hT.2.2
    obtain ⟨l0', l1'⟩ := h'.1.encOutLength
    exact Or.inl (serealizeExternalData_inj T T' hT.2.1 h'.1.amountRange l0 l1 l0' l1' hser)
  · refine Or.inr ⟨hser, ?_⟩
    have hb := hT.1
    have hb' := h'.1.externalDataBinding
    unfold externalDataBound externalDataHash at hb hb'
    rw [hb, hb']
    exact congrArg PubInputs.extDataHash hSame

-- PROOF of G2b. Statement and explanation: `Spec/Statements.lean`.
theorem shared_nullifier_requires_owner_key
    (x x' : PubInputs) (w w' : Witness) (hRel : RelationS x w) (hRel' : RelationS x' w')
    (i i' : Fin 2) (hShared : x.nullifiers i = x'.nullifiers i') :
    w'.inSk i' = w.inSk i
    ∨ H3Collision (w.nullifierArgs i) (w'.nullifierArgs i')
    ∨ H4Collision (w.inNote i) (w'.inNote i')
    ∨ H1Collision (w.inSk i) (w'.inSk i') := by
  rw [hRel.nullifierCorrectness i, hRel'.nullifierCorrectness i'] at hShared
  by_cases hargs : w.nullifierArgs i = w'.nullifierArgs i'
  · have hC : w.inC i = w'.inC i' := congrArg Prod.fst hargs
    rcases commitment_determines_value_or_collision _ _ _ _ _ _ _ _ hC with heq | hH4
    · have hpk : H1 (w.inSk i) = H1 (w'.inSk i') := congrArg Note.ownerPk heq
      by_cases hsk : w.inSk i = w'.inSk i'
      · exact Or.inl hsk.symm
      · exact Or.inr (Or.inr (Or.inr ⟨hsk, hpk⟩))
    · exact Or.inr (Or.inr (Or.inl hH4))
  · exact Or.inr (Or.inl ⟨hargs, hShared⟩)

/-! ## G3. Liveness -/

-- LEMMA (used by G3b): `transferEffects` doesn't touch the nullifier set.
lemma transferEffects_nullifiers (inputs: TxInputs) (oldWorld: World) :
    (transferEffects inputs oldWorld).state.nullifiers = oldWorld.state.nullifiers := by
  unfold transferEffects
  split_ifs <;> rfl

-- LEMMA (used by G3b): every nullifier in the set was revealed by a transaction of the run.
lemma Run.nullifier_origin {params : InitParams}
    (r : Run (initWorld params)) :
    ∀ j ≤ r.txs.length, ∀ x ∈ (r.ws j).state.nullifiers,
      ∃ j', ∃ (hj' : j' < r.txs.length), ∃ i, r.txs[j'].pubInputs.nullifiers i = x := by
  intro j
  induction j with
  | zero => intro _ x hx; rw [r.start] at hx; simp [initWorld] at hx
  | succ j ih =>
    intro hj x hx
    have hjn : j < r.txs.length := by omega
    obtain ⟨_, hagree⟩ := r.step j hjn
    rw [hagree.nullifiers] at hx
    simp only [transactEffects, transferEffects_nullifiers, nullifierRentEffects_state, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton] at hx
    rcases hx with hx | hx | hx
    · exact ih (by omega) x hx
    · exact ⟨j, hjn, 0, by simp [TxInputs.pubInputs, hx]⟩
    · exact ⟨j, hjn, 1, by simp [TxInputs.pubInputs, hx]⟩

-- LEMMA (used by G3b): leaf indices are below `p`, so equal as field elements means equal.
lemma leafIndex_cast_inj (a b : Fin (2^26)) (h : ((a : ℕ) : F) = ((b : ℕ) : F)) : a = b := by
  have hmod := (ZMod.natCast_eq_natCast_iff' (a : ℕ) (b : ℕ) p).mp h
  have hp : 2^26 < p := by norm_num [p]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
  exact Fin.ext hmod

-- PROOF of G3b. Statement and explanation: `Spec/Statements.lean`.
theorem unspent_note_cannot_be_blocked
    (params : InitParams)
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)
    (w : Witness) (i : Fin 2) (hne : w.inAmt i ≠ 0)
    (hpos : (w.openings i).index.val ∈ r.unspent wit) :
    nullifier (w.inC i) (w.sign i) (w.openings i).index ∉ r.final.state.nullifiers
    ∨ NullifierTaken r wit w i := by
  classical
  by_cases hmem : nullifier (w.inC i) (w.sign i) (w.openings i).index ∈ r.final.state.nullifiers
  swap; · exact Or.inl hmem
  right
  obtain ⟨j, hj, i', hji⟩ := r.nullifier_origin r.txs.length le_rfl _ hmem
  refine ⟨j, hj, i', hji, ?_⟩
  have hH3 : H3 (w.nullifierArgs i).1 (w.nullifierArgs i).2.1 (w.nullifierArgs i).2.2
      = H3 ((wit j).nullifierArgs i').1 ((wit j).nullifierArgs i').2.1 ((wit j).nullifierArgs i').2.2 := by
    have := (hwit.relation j hj).nullifierCorrectness i'
    rw [hji] at this
    exact this
  by_cases hargs : w.nullifierArgs i = (wit j).nullifierArgs i'
  swap; · exact Or.inl ⟨hargs, hH3⟩
  have hC : w.inC i = (wit j).inC i' := congrArg Prod.fst hargs
  have hIdx : (w.openings i).index = ((wit j).openings i').index :=
    leafIndex_cast_inj _ _ (congrArg (fun a => a.2.1) hargs)
  rcases commitment_determines_value_or_collision _ _ _ _ _ _ _ _ hC with heq | hH4
  · -- the same note, so the same non-zero amount: input `i'` spent this very note
    exfalso
    have hamt : (wit j).inAmt i' ≠ 0 := by
      have : w.inAmt i = (wit j).inAmt i' := congrArg Note.amount heq
      rw [← this]; exact hne
    simp only [Run.unspent, Finset.mem_filter] at hpos
    exact hpos.2 ⟨j, hj, i', hamt, by simp only [spentLeaf]; rw [hIdx]⟩
  · exact Or.inr hH4

-- LEMMA (used by G3a): a dummy input whose secret key no input of the run uses has a fresh
-- nullifier, unless an `H3` collision occurs. Equal nullifiers mean equal signatures (or an
-- `H3` collision), and equal signatures mean equal secret keys (or an `H3` collision).
lemma dummy_nullifier_free
    (params : InitParams)
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)
    (w : Witness) (i : Fin 2)
    (hkey : ∀ j < r.txs.length, ∀ i', (wit j).inSk i' ≠ w.inSk i) :
    nullifier (w.inC i) (w.sign i) (w.openings i).index ∉ r.final.state.nullifiers
    ∨ DummyNullifierTaken r wit w i := by
  classical
  by_cases hmem : nullifier (w.inC i) (w.sign i) (w.openings i).index ∈ r.final.state.nullifiers
  swap; · exact Or.inl hmem
  right
  obtain ⟨j, hj, i', hji⟩ := r.nullifier_origin r.txs.length le_rfl _ hmem
  refine ⟨j, hj, i', hji, ?_⟩
  have hH3 : H3 (w.nullifierArgs i).1 (w.nullifierArgs i).2.1 (w.nullifierArgs i).2.2
      = H3 ((wit j).nullifierArgs i').1 ((wit j).nullifierArgs i').2.1 ((wit j).nullifierArgs i').2.2 := by
    have := (hwit.relation j hj).nullifierCorrectness i'
    rw [hji] at this
    exact this
  by_cases hargs : w.nullifierArgs i = (wit j).nullifierArgs i'
  swap; · exact Or.inl ⟨hargs, hH3⟩
  have hsign : H3 (w.signatureArgs i).1 (w.signatureArgs i).2.1 (w.signatureArgs i).2.2
      = H3 ((wit j).signatureArgs i').1 ((wit j).signatureArgs i').2.1 ((wit j).signatureArgs i').2.2 :=
    congrArg (fun a => a.2.2) hargs
  by_cases hsargs : w.signatureArgs i = (wit j).signatureArgs i'
  · exact absurd (congrArg Prod.fst hsargs).symm (hkey j hj i')
  · exact Or.inr ⟨hsargs, hsign⟩

-- LEMMA (used by G3a): a withdrawal that spends unspent notes never fails on pool
-- solvency, because G1c makes the pool hold at least the value of those notes.
lemma withdrawal_solvent
    (params : InitParams)
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)
    (inputs : TxInputs) (witness : Witness)
    (hNotes : ∀ i, witness.inAmt i ≠ 0 → (witness.openings i).index.val ∈ r.unspent wit
        ∧ witness.inNote i = leafNote wit (witness.openings i).index.val)
    (hTwo : witness.inAmt 0 ≠ 0 → witness.inAmt 1 ≠ 0 →
        (witness.openings 0).index ≠ (witness.openings 1).index)
    (hAC : witness.inAmt 0 + witness.inAmt 1 + inputs.pubInputs.pubAmt
        = witness.outAmt 0 + witness.outAmt 1)
    (hOR : ∀ j, (witness.outAmt j).val < 2^248)
    (hPubAmt : pubAmtConsistent inputs.extAmt inputs.f inputs.pubAmt)
    (hRange : amountsInRange inputs.extAmt inputs.f) :
    (inputs.extAmt < 0 →
      (r.final.poolBalance : ℤ) ≥ |inputs.extAmt| + inputs.f + r.final.rentExemptMin)
    ∨ BalanceBreak r wit := by
  classical
  rcases balance params r wit hwit with hbal | hbrk
  swap; · exact Or.inr hbrk
  left
  intro hneg
  have hrent : r.final.rentExemptMin = params.rentExemptMin :=
    (config_and_rent_exempt_min_constant params _ (r.reachable _ le_rfl)).2
  -- each spent input is worth exactly its note, which is below 2^248
  have hval : ∀ i, witness.inAmt i ≠ 0 →
      (((witness.inAmt i).val : ℤ) = leafValue wit (witness.openings i).index.val)
      ∧ (witness.inAmt i).val < 2^248 := by
    intro i hne
    obtain ⟨hmem, hnote⟩ := hNotes i hne
    have hlt : (witness.openings i).index.val < 2 * r.txs.length := by
      simp only [Run.unspent, Finset.mem_filter, Finset.mem_range] at hmem; exact hmem.1
    have hamt : witness.inAmt i = (leafNote wit (witness.openings i).index.val).amount :=
      congrArg Note.amount hnote
    refine ⟨by rw [hamt]; rfl, ?_⟩
    rw [hamt]
    exact (hwit.relation ((witness.openings i).index.val / 2) (by omega)).outputRangeChecks _
  obtain ⟨hr1, hr2, hr3⟩ := hRange
  have hdelta := value_delta_eq_ext_sub_fee witness inputs.pubInputs inputs.extAmt inputs.f hAC hOR
    hPubAmt (fun i hne => (hval i hne).2) (by omega) (by omega)
  have hnn : ∀ pos, 0 ≤ leafValue wit pos := fun pos => by unfold leafValue; positivity
  -- the unspent notes are worth at least the two inputs
  have hsum : (((witness.inAmt 0).val : ℤ) + (witness.inAmt 1).val)
      ≤ ∑ pos ∈ r.unspent wit, leafValue wit pos := by
    by_cases h0 : witness.inAmt 0 = 0 <;> by_cases h1 : witness.inAmt 1 = 0
    · rw [h0, h1, ZMod.val_zero]; simp only [Nat.cast_zero, add_zero]
      exact Finset.sum_nonneg (fun pos _ => hnn pos)
    · rw [h0, ZMod.val_zero, Nat.cast_zero, zero_add, (hval 1 h1).1]
      exact Finset.single_le_sum (fun pos _ => hnn pos) (hNotes 1 h1).1
    · rw [h1, ZMod.val_zero, Nat.cast_zero, add_zero, (hval 0 h0).1]
      exact Finset.single_le_sum (fun pos _ => hnn pos) (hNotes 0 h0).1
    · rw [(hval 0 h0).1, (hval 1 h1).1]
      have hne : (witness.openings 0).index.val ≠ (witness.openings 1).index.val :=
        fun h => hTwo h0 h1 (Fin.ext h)
      rw [← Finset.sum_pair hne]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro pos hp
        simp only [Finset.mem_insert, Finset.mem_singleton] at hp
        rcases hp with rfl | rfl
        · exact (hNotes 0 h0).1
        · exact (hNotes 1 h1).1
      · exact fun pos _ _ => hnn pos
  have habs : |inputs.extAmt| = -inputs.extAmt := abs_of_neg hneg
  rw [hrent, ge_iff_le, habs]
  show _ ≤ ((r.ws r.txs.length).poolBalance : ℤ)
  have hfinal : ((r.ws r.txs.length).poolBalance : ℤ)
      = params.rentExemptMin + ∑ pos ∈ r.unspent wit, leafValue wit pos := hbal
  have ho : (0 : ℤ) ≤ (witness.outAmt 0).val + (witness.outAmt 1).val := by positivity
  linarith

-- LEMMA (used by G3a): G3a with every hypothesis spelled out.
lemma spendable_core
    (params : InitParams) (hCompl : Groth16Complete)
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)
    (inputs: TxInputs) (witness: Witness)
    -- the root: present in the history, and the root of the first `k` leaves
    (k : ℕ) (hk : k ≤ 2 * r.txs.length)
    (hRk : inputs.R = (foldAppend ((leaves r.txs).take k) initTree).root)
    (hRwin : inputs.R ∈ Set.range r.final.state.tree.history)
    -- the owner's notes: distinct unspent notes among the first `k` leaves
    (hNotes : ∀ i, witness.inAmt i ≠ 0 → (witness.openings i).index.val < k
        ∧ (witness.openings i).index.val ∈ r.unspent wit
        ∧ witness.inNote i = leafNote wit (witness.openings i).index.val)
    (hTwo : witness.inAmt 0 ≠ 0 → witness.inAmt 1 ≠ 0 →
        (witness.openings 0).index ≠ (witness.openings 1).index)
    -- each zero-amount input uses a fresh secret key: one that no input of the run uses
    (hDummyKey : ∀ i, witness.inAmt i = 0 →
        ∀ j < r.txs.length, ∀ i', (wit j).inSk i' ≠ witness.inSk i)
    -- the transaction is built honestly from the witness
    (hOutputCommitmentIntegrity : ∀ j, inputs.pubInputs.outCommitments j
        = commit (witness.outAmt j) (witness.outPk j) (witness.outR j) witness.mint)
    (hNullifierCorrectness : ∀ i, inputs.pubInputs.nullifiers i
        = nullifier (witness.inC i) (witness.sign i) (witness.openings i).index)
    (hNoDuplicateNullifiers : inputs.pubInputs.nullifiers 0 ≠ inputs.pubInputs.nullifiers 1)
    (hAmountConservation : witness.inAmt 0 + witness.inAmt 1 + inputs.pubInputs.pubAmt
        = witness.outAmt 0 + witness.outAmt 1)
    (hOutputRangeChecks : ∀ j, (witness.outAmt j).val < 2^248)
    (hData: externalDataBound inputs)
    (hPubAmt: pubAmtConsistent inputs.extAmt inputs.f inputs.pubAmt)
    (hDistinct: nullifiersDistinct inputs.k0 inputs.k1)
    (hRange: amountsInRange inputs.extAmt inputs.f)
    (hEnc: encOutsFit inputs)
    (hSep: poolIsSeparate inputs r.final.state.pool)
    -- policy checks
    (hFee: feeSufficient r.final.state.config inputs.extAmt inputs.f)
    (hDeposit: depositWithinLimit r.final.state.config inputs.extAmt)
    (hDepositFee: inputs.extAmt ≥ 0 ∧ inputs.f > 0 →
        (r.final.poolBalance : ℤ) + inputs.extAmt ≥ inputs.f + r.final.rentExemptMin)
    (hSignerSolvent: signerSolvent r.final.balances inputs.s inputs.extAmt r.final.nullifierRent)
    (hRoom: treeHasRoom r.final.state.tree) :
    (∃ π, transact { inputs with π := π } r.final (transactEffects { inputs with π := π } r.final))
    ∨ H2ZeroPreimage (treeHash ((leaves r.txs).take k) 25 0, treeHash ((leaves r.txs).take k) 25 1)
    ∨ BalanceBreak r wit
    ∨ (∃ i, witness.inAmt i ≠ 0 ∧ NullifierTaken r wit witness i)
    ∨ (∃ i, witness.inAmt i = 0 ∧ DummyNullifierTaken r wit witness i) := by
  classical
  by_cases hR0 : inputs.R = 0
  · -- the root of the first `k` leaves is `H2` of its two subtrees
    refine Or.inr (Or.inl ⟨?_⟩)
    have hcapk : ((leaves r.txs).take k).length < 2^26 := by
      rw [List.length_take]; have := hRoom; unfold treeHasRoom at this; rw [r.final_nextIndex] at this; omega
    have hroot := (foldAppend_spec _ hcapk).2.1
    rw [← hRk, hR0] at hroot
    have h26 : treeHash ((leaves r.txs).take k) (25 + 1) 0
        = H2 (treeHash ((leaves r.txs).take k) 25 0) (treeHash ((leaves r.txs).take k) 25 1) := by
      rw [treeHash.eq_2]
    show H2 (treeHash ((leaves r.txs).take k) 25 0) (treeHash ((leaves r.txs).take k) 25 1) = 0
    rw [← h26]
    exact hroot.symm
  by_cases hB : BalanceBreak r wit
  · exact Or.inr (Or.inr (Or.inl hB))
  by_cases hT : ∃ i, witness.inAmt i ≠ 0 ∧ NullifierTaken r wit witness i
  · exact Or.inr (Or.inr (Or.inr (Or.inl hT)))
  by_cases hD : ∃ i, witness.inAmt i = 0 ∧ DummyNullifierTaken r wit witness i
  · exact Or.inr (Or.inr (Or.inr (Or.inr hD)))
  left
  -- the nullifiers are free: G3b for the owner's notes, the dummy-key lemma for the rest
  have hfree : ∀ i, inputs.pubInputs.nullifiers i ∉ r.final.state.nullifiers := by
    intro i
    rw [hNullifierCorrectness i]
    by_cases hz : witness.inAmt i = 0
    · rcases dummy_nullifier_free params r wit hwit witness i
          (hDummyKey i hz) with h | h
      · exact h
      · exact absurd ⟨i, hz, h⟩ hD
    ·
      rcases unspent_note_cannot_be_blocked params r wit hwit witness i
          hz (hNotes i hz).2.1 with h | h
      · exact h
      · exact absurd ⟨i, hz, h⟩ hT
  have hFresh : nullifiersFresh r.final.state.nullifiers inputs.k0 inputs.k1 :=
    ⟨hfree 0, hfree 1⟩
  -- the pool can pay: from G1c
  have hSolvent : poolSolvent r.final.poolBalance r.final.rentExemptMin inputs.extAmt inputs.f := by
    refine ⟨?_, hDepositFee⟩
    rcases withdrawal_solvent params r wit hwit inputs witness
        (fun i hne => (hNotes i hne).2) hTwo hAmountConservation hOutputRangeChecks hPubAmt
        hRange with h | h
    · exact h
    · exact absurd h hB
  have hRoot : rootKnown r.final.state.tree inputs.R := ⟨hRwin, hR0⟩
  have hlen : (leaves r.txs).length = 2 * r.txs.length := leaves_length r.txs
  have hcap : ((leaves r.txs).take k ++ []).length < 2^26 := by
    rw [List.append_nil, List.length_take]; have := hRoom; unfold treeHasRoom at this; rw [r.final_nextIndex] at this; omega
  -- each spent note is the leaf at its position, with the owner's commitment
  have hDep : ∀ i, witness.inAmt i ≠ 0 →
      (witness.openings i).index.val < ((leaves r.txs).take k).length
      ∧ leafAt ((leaves r.txs).take k) (witness.openings i).index.val = witness.inC i := by
    intro i hne
    obtain ⟨hlt, _, hnote⟩ := hNotes i hne
    refine ⟨by rw [List.length_take]; omega, ?_⟩
    rw [leafAt_take _ _ _ hlt]
    set pos := (witness.openings i).index.val with hpos_def
    have hm : pos / 2 < r.txs.length := by omega
    have hpos : pos = 2 * (pos / 2) + (⟨pos % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2).val := by
      simp only; omega
    rw [hpos, leafAt_leaves _ _ hm, (hwit.relation _ hm).outputCommitmentIntegrity]
    simp only [Witness.inNote, leafNote, Witness.outNote, Note.mk.injEq] at hnote
    obtain ⟨h1, h2, h3, h4⟩ := hnote
    simp only [Witness.inC, commit]
    rw [h1, h2, h3, h4]
  exact transact_complete hCompl r.final inputs witness ((leaves r.txs).take k) [] hcap
    (by rw [List.append_nil]; exact hRk) hDep
    hOutputCommitmentIntegrity hNullifierCorrectness hNoDuplicateNullifiers hAmountConservation
    hOutputRangeChecks hRoot hData hFee hPubAmt hFresh hDistinct hDeposit hSolvent
    hSignerSolvent hRoom hRange hEnc hSep

-- PROOF of G3a. Statement and explanation: `Spec/Statements.lean`.
theorem unspent_note_is_spendable
    -- [premise] a pool initialized with `params`; [trust T1] Groth16 completeness
    (params : InitParams) (hCompl : Groth16Complete)
    -- [attacker] any history; [trust T1] the witnesses behind its proofs
    (r : Run (initWorld params)) (wit : ℕ → Witness) (hwit : r.WitnessesFor wit)
    -- [owner] the owner's transaction, its secrets, and the tree state it uses
    (inputs : TxInputs) (witness : Witness) (k : ℕ)
    (hRoot : RootInWindow r inputs.R k)
    (hNotes : OwnsUnspentNotes r wit witness k)
    (hHonest : BuiltHonestly r.final inputs witness)
    (hPolicy : PolicyChecksPass r.final inputs) :
    CanBeAccepted inputs r.final ∨ LivenessBreak r wit witness k := by
  rcases spendable_core params hCompl r wit hwit inputs witness k hRoot.isPrefix hRoot.isPrefixRoot
      hRoot.inWindow (fun i hne => ⟨hNotes.inTree i hne, hNotes.unspent i hne, hNotes.isOwnersNote i hne⟩)
      hNotes.different hNotes.freshDummyKeys hHonest.outputs hHonest.nullifiers
      hHonest.distinctNullifiers hHonest.amounts hHonest.outputRange hHonest.externalData
      hHonest.publicAmount hHonest.distinctNullifiers hHonest.amountRange hHonest.encOutLength
      hHonest.poolSeparate hPolicy.fee hPolicy.depositLimit hPolicy.depositFee
      hHonest.signerCanPay hPolicy.treeRoom with h | h
  · exact Or.inl h
  · exact Or.inr h

-- PROOF of G3c. Statement and explanation: `Spec/Statements.lean`.
theorem full_tree_freezes_pool
    (params : InitParams)
    (r : Run (initWorld params)) (hfull : 2^25 ≤ r.txs.length)
    (inputs : TxInputs) (newWorld : World) :
    ¬ transact inputs r.final newWorld := by
  intro h
  have hroom := h.1.treeNotFull
  unfold treeHasRoom at hroom
  have htree := (r.tree r.txs.length le_rfl).1
  rw [show r.final = r.ws r.txs.length from rfl, htree, foldAppend_nextIndex,
    r.leaves_take_length _ le_rfl] at hroom
  omega

/-! ## G4. Correct public payouts -/

-- PROOF of G4a. Statement and explanation: `Spec/Statements.lean`.
theorem no_sol_created
    (oldWorld newWorld : World) (inputs : TxInputs) (h : transact inputs oldWorld newWorld) :
    ∑ k ∈ ({inputs.s, inputs.A, inputs.t, oldWorld.state.pool} : Finset Pubkey),
        (newWorld.balances k : ℤ)
    = ∑ k ∈ ({inputs.s, inputs.A, inputs.t, oldWorld.state.pool} : Finset Pubkey),
        (oldWorld.balances k : ℤ)
      - 2 * oldWorld.nullifierRent := by
  classical
  obtain ⟨hpre, hagree⟩ := h
  set S : Finset Pubkey := {inputs.s, inputs.A, inputs.t, oldWorld.state.pool}
  have hnew : ∑ k ∈ S, (newWorld.balances k : ℤ)
      = ∑ k ∈ S, (oldWorld.balances k : ℤ)
        + ∑ k ∈ S, balanceDelta inputs oldWorld.state.pool oldWorld.nullifierRent k := by
    rw [← Finset.sum_add_distrib, hagree.balances]
    exact Finset.sum_congr rfl (fun k _ => transactEffects_balances inputs oldWorld
      hpre.signerSolvency hpre.poolSolvency hpre.poolSeparate k)
  have hdelta : ∑ k ∈ S, balanceDelta inputs oldWorld.state.pool oldWorld.nullifierRent k
      = (if inputs.extAmt < 0 then (inputs.extAmt.natAbs : ℤ) else 0) + inputs.f
        - (if inputs.extAmt > 0 then inputs.extAmt else 0) - 2 * oldWorld.nullifierRent
        + (inputs.extAmt - inputs.f) := by
    unfold balanceDelta
    simp only [ite_and, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq', Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp [S]
  have hext : (if inputs.extAmt < 0 then (inputs.extAmt.natAbs : ℤ) else 0)
      - (if inputs.extAmt > 0 then inputs.extAmt else 0) + inputs.extAmt = 0 := by
    split_ifs <;> omega
  linarith

-- PROOF of G4b. Statement and explanation: `Spec/Statements.lean`.
theorem balance_changes_exact
    (oldWorld newWorld : World) (inputs : TxInputs) (h : transact inputs oldWorld newWorld)
    (k : Pubkey) :
    (newWorld.balances k : ℤ)
      = oldWorld.balances k + balanceDelta inputs oldWorld.state.pool oldWorld.nullifierRent k := by
  obtain ⟨hpre, hagree⟩ := h
  rw [hagree.balances]
  exact transactEffects_balances inputs oldWorld hpre.signerSolvency hpre.poolSolvency
    hpre.poolSeparate k

/-! ## G5. Config immutability -/

-- PROOF of G5. Statement and explanation: `Spec/Statements.lean`.
theorem config_constant
    (params : InitParams)
    (r : Run (initWorld params)) :
    ∀ j ≤ r.txs.length, (r.ws j).state.config = params.cfg ∧ (r.ws j).rentExemptMin = params.rentExemptMin :=
  fun j hj => config_and_rent_exempt_min_constant params _ (r.reachable j hj)

end LeanSpec
