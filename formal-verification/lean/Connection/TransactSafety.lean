import Connection.Basic
open Aeneas Aeneas.Std Result ControlFlow
open LeanSpec (F)

/-! # Safety of `fv_transact_entry`: code accepts ⟹ spec `transact` holds

Inversion lemmas first: from "`x >>= k` returned `ok v`", recover what `x` returned. -/

theorem bindOkInv {α β : Type} {x : Result α} {k : α → Result β} {v : β}
    (h : x >>= k = ok v) : ∃ a, x = ok a ∧ k a = ok v := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind, Aeneas.Std.bind] at h
  | div => simp [Bind.bind, Aeneas.Std.bind] at h

theorem branchOkInv {T E : Type} {r : core.result.Result T E}
    {cf : core.ops.control_flow.ControlFlow (core.result.Result core.convert.Infallible E) T}
    (h : core.result.Result.Insts.CoreOpsTry.branch r = ok cf) :
    (∃ v, r = .Ok v ∧ cf = .Continue v) ∨ (∃ e, r = .Err e ∧ cf = .Break (.Err e)) := by
  cases r with
  | Ok v => left; exact ⟨v, rfl, by simp [core.result.Result.Insts.CoreOpsTry.branch] at h; exact h.symm⟩
  | Err e => right; exact ⟨e, rfl, by simp [core.result.Result.Insts.CoreOpsTry.branch] at h; exact h.symm⟩

/-- Peel one `let x ← step` off `h : (do let x ← step; …) = ok v`. -/
macro "peel " h:ident " as " a:ident ha:ident : tactic =>
  `(tactic| obtain ⟨$a, $ha, $h⟩ := bindOkInv $h)

/-- Close a rejection branch: whatever its steps return (including the diagnostic axioms),
it ends in `ok (.Err _, …)` or fails, never `ok (.Ok (), …)`. -/
macro "reject " h:ident : tactic =>
  `(tactic| (
    try simp only [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      bind_assoc_eq, bind_tc_ok] at $h:ident
    repeat (obtain ⟨_, _, $h:ident⟩ := bindOkInv $h:ident)
    simp at $h:ident))

/-- Split on a `checked_*` result fed through `ok_or`/`?`: the `none` case is a rejection
(closed by `reject`), the `some v` case continues with `hv : o = some v`. -/
macro "unwrap " h:ident " : " o:term " as " v:ident hv:ident : tactic =>
  `(tactic| (
    rcases $hv:ident : $o:term with _ | $v:ident
    · simp only [$hv:ident, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
        bind_tc_ok] at $h:ident
      reject $h
    simp only [$hv:ident, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok] at $h:ident))

theorem indexOk {α : Type} [Inhabited α] {n : Std.Usize} (a : Array α n) (i : Std.Usize) (c : α)
    (h : Array.index_usize a i = ok c) : c = a.val[i.val]! := by
  have hlt : i.val < a.val.length := by
    by_contra hc
    simp [Array.index_usize, List.getElem?_eq_none (by omega : a.val.length ≤ i.val)] at h
  have hs := Array.index_usize_spec a i (by scalar_tac)
  rw [h] at hs
  have := (WP.spec_ok _).mp hs
  rw [getElem!_pos a.val i.val hlt]; simpa using this

theorem u64SubVal {x y z : Std.U64} (h : x.checked_sub y = some z) :
    y.val ≤ x.val ∧ z.val = x.val - y.val := by
  have hs := U64.checked_sub_bv_spec x y; rw [h] at hs; exact ⟨hs.1, hs.2.1⟩

theorem u64AddVal {x y z : Std.U64} (h : x.checked_add y = some z) :
    z.val = x.val + y.val := by
  have hs := U64.checked_add_bv_spec x y; rw [h] at hs; exact hs.2.1

theorem usizeRemVal {x y z : Std.Usize} (hy : y.val ≠ 0) (h : x % y = ok z) :
    z.val = x.val % y.val := by
  have hs := UScalar.rem_spec x hy
  rw [h] at hs; exact (WP.spec_ok _).mp hs

theorem fromElemLen (n : Std.Usize) (pr : alloc.vec.Vec (Array Std.U8 32#usize))
    (h : alloc.vec.from_elem (core.clone.CloneArray 32#usize core.clone.CloneU8)
      (Array.repeat 32#usize 0#u8) n = ok pr) : pr.length = n.val := by
  have hc : (core.clone.CloneArray 32#usize core.clone.CloneU8).clone (Array.repeat 32#usize 0#u8)
      = ok (Array.repeat 32#usize 0#u8) := by
    have hs := core.array.CloneArray.clone_spec core.clone.CloneU8 (Array.repeat 32#usize 0#u8)
      (by intro x _; rfl)
    cases hcl : core.array.CloneArray.clone core.clone.CloneU8 (Array.repeat 32#usize 0#u8) with
    | ok a' =>
      rw [hcl] at hs
      show core.array.CloneArray.clone core.clone.CloneU8 _ = _
      rw [hcl, ← (WP.spec_ok _).mp hs]
    | fail e => rw [hcl] at hs; simp at hs
    | div => rw [hcl] at hs; simp at hs
  have hs := alloc.vec.from_elem_spec _ _ n hc
  rw [h] at hs; exact ((WP.spec_ok _).mp hs).2

/-- A successful `append` changes only the tree-shaped fields: `height`,
`root_history_size` and `max_deposit_amount` are untouched, and `next_index` goes up by one.
Needs nothing about the hasher or the loop, only that every step returned. -/
theorem appendStruct (leaf : Array Std.U8 32#usize) (ta ta' : zkcash.MerkleTreeAccount)
    (p : alloc.vec.Vec (Array Std.U8 32#usize))
    (h : zkcash.merkle_tree.MerkleTree.append
        zkcash.light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher leaf ta
      = ok (.Ok p, ta')) :
    ta'.height = ta.height ∧ ta'.root_history_size = ta.root_history_size ∧
      ta'.max_deposit_amount = ta.max_deposit_amount ∧
      ta'.next_index.val = ta.next_index.val + 1 ∧
      (ta.root_history_size.val = 100 → ta'.root_index.val < 100) := by
  unfold zkcash.merkle_tree.MerkleTree.append at h
  simp only [lift, bind_tc_ok] at h
  peel h as mc hmc
  split_ifs at h with hroom
  · peel h as pr hpr
    peel h as lp hlp
    obtain ⟨a1, hroot, proof1⟩ := lp
    unwrap h : ta.next_index.checked_add 1#u64 as val hval
    unwrap h : Usize.checked_add (UScalar.cast UScalarTy.Usize ta.root_index) 1#usize as val1 hval1
    peel h as nri hnri
    peel h as a2 ha2
    simp only [ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    have hv := U64.checked_add_bv_spec ta.next_index 1#u64
    rw [hval] at hv
    refine ⟨rfl, rfl, rfl, by simpa using hv.2.1, fun hs => ?_⟩
    have hsz : (UScalar.cast .Usize ta.root_history_size).val = 100 := by simp [hs]
    have hn := usizeRemVal (by rw [hsz]; norm_num) hnri
    have hlt : nri.val < 100 := by rw [hn, hsz]; exact Nat.mod_lt _ (by norm_num)
    show (UScalar.cast .U64 nri).val < 100
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simp; omega)]; exact hlt
  · reject h

/-! ## `append`: the Merkle loop computes `appendEffects`

The spec folds 26 levels with `Fin.foldl`; the code runs `append_loop` 26 times. `natFold`
is the same fold indexed by `ℕ`, so the loop invariant can talk about "the first `k`
levels". -/

/-- `k` steps of a fold indexed by `ℕ`. -/
def natFold {α : Type} (g : α → ℕ → α) (x : α) : ℕ → α
  | 0 => x
  | k + 1 => g (natFold g x k) k

theorem finFoldlNat {α : Type} (g : α → ℕ → α) :
    ∀ (n : ℕ) (x : α), Fin.foldl n (fun a (j : Fin n) => g a j.val) x = natFold g x n
  | 0, x => by simp [natFold]
  | n + 1, x => by
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [finFoldlNat g n x]; rfl

/-- One level of `appendEffects`'s fold (levels `≥ 26` are no-ops, to make it total on `ℕ`). -/
def appendLevel [LeanSpec.PoseidonHashes] (index : ℕ) (acc : F × (Fin 26 → F)) (j : ℕ) :
    F × (Fin 26 → F) :=
  if hj : j < 26 then
    if Nat.testBit index j then (LeanSpec.PoseidonHashes.H2 (acc.2 ⟨j, hj⟩) acc.1, acc.2)
    else (LeanSpec.PoseidonHashes.H2 acc.1 (LeanSpec.Z j), Function.update acc.2 ⟨j, hj⟩ acc.1)
  else acc

theorem appendEffectsFold [LeanSpec.PoseidonHashes] (c : F) (t : LeanSpec.Tree) :
    LeanSpec.appendEffects c t =
      let r := natFold (appendLevel t.nextIndex) (c, t.subtrees) 26
      { nextIndex := t.nextIndex + 1, subtrees := r.2, root := r.1,
        history := Function.update t.history (t.rootIndex + 1) r.1,
        rootIndex := t.rootIndex + 1 } := by
  have hf : ∀ x, Fin.foldl 26 (fun (p : F × (Fin 26 → F)) (height : Fin 26) =>
      match p with
      | (current, subtrees) =>
        if Nat.testBit t.nextIndex height.val then
          (LeanSpec.PoseidonHashes.H2 (subtrees height) current, subtrees)
        else (LeanSpec.PoseidonHashes.H2 current (LeanSpec.Z height.val),
          Function.update subtrees height current)) x
      = natFold (appendLevel t.nextIndex) x 26 := by
    intro x
    rw [← finFoldlNat]
    congr 1; funext acc j; obtain ⟨cur, sub⟩ := acc
    simp [appendLevel, j.isLt]
  simp only [LeanSpec.appendEffects, hf]

/-- The 32-byte arrays of a 26-entry array, read as field elements. -/
def mapSubtrees (a : Array (Array Std.U8 32#usize) 26#usize) : Fin 26 → F :=
  fun j => mapBytesToF a.val[j.val]!

theorem mapSubtreesSet (a : Array (Array Std.U8 32#usize) 26#usize) (i : Std.Usize)
    (v : Array Std.U8 32#usize) (hi : i.val < 26) :
    mapSubtrees (a.set i v) = Function.update (mapSubtrees a) ⟨i.val, hi⟩ (mapBytesToF v) := by
  funext j
  have hlen : a.val.length = 26 := by simp
  by_cases hj : j = ⟨i.val, hi⟩
  · subst hj
    simp only [mapSubtrees, Function.update_self, Array.set_val_eq]
    rw [getElem!_pos _ _ (by simpa [hlen] using hi)]
    simp
  · have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp only [mapSubtrees, Function.update_of_ne hj, Array.set_val_eq]
    rw [getElem!_pos _ _ (by simp [hlen]), getElem!_pos _ _ (by simp [hlen])]
    simp [Ne.symm hj']

theorem appendLoopSpec [LeanSpec.PoseidonHashes] (index : ℕ) (init : F × (Fin 26 → F))
    (hHashv : ∀ a b : Array Std.U8 32#usize, ∃ h : Array Std.U8 32#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.hashv
          ⟨[⟨a.val, by scalar_tac⟩, ⟨b.val, by scalar_tac⟩], by scalar_tac⟩
        = ok (core.result.Result.Ok h) ∧
        mapBytesToF h = LeanSpec.PoseidonHashes.H2 (mapBytesToF a) (mapBytesToF b))
    (zeroBytes : Array (Array Std.U8 32#usize) 41#usize)
    (hzb : light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.zero_bytes = ok zeroBytes)
    (hZ : ∀ i : Fin 26, mapBytesToF (zeroBytes.val[i.val]!) = LeanSpec.Z i.val)
    (iter : core.ops.range.Range Std.Usize) (a : Array (Array Std.U8 32#usize) 26#usize)
    (ci : Std.Usize) (cur : Array Std.U8 32#usize) (proof : alloc.vec.Vec (Array Std.U8 32#usize))
    (hk : iter.start.val ≤ 26) (hend : iter.end.val = 26)
    (hci : ci.val = index / 2 ^ iter.start.val) (hplen : proof.length = 26)
    (hst : (mapBytesToF cur, mapSubtrees a) = natFold (appendLevel index) init iter.start.val) :
    zkcash.merkle_tree.MerkleTree.append_loop
        zkcash.light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher iter a ci cur proof
      ⦃ (r : (Array (Array Std.U8 32#usize) 26#usize) × (Array Std.U8 32#usize) ×
          (alloc.vec.Vec (Array Std.U8 32#usize))) =>
        (mapBytesToF r.2.1, mapSubtrees r.1) = natFold (appendLevel index) init 26 ⦄ := by
  unfold zkcash.merkle_tree.MerkleTree.append_loop
  apply loop.spec_decr_nat
    (measure := fun x : (core.ops.range.Range Std.Usize) × (Array (Array Std.U8 32#usize) 26#usize)
        × Std.Usize × (Array Std.U8 32#usize) × (alloc.vec.Vec (Array Std.U8 32#usize)) =>
      26 - x.1.start.val)
    (inv := fun x => x.1.start.val ≤ 26 ∧ x.1.end.val = 26 ∧
      x.2.2.1.val = index / 2 ^ x.1.start.val ∧ x.2.2.2.2.length = 26 ∧
      (mapBytesToF x.2.2.2.1, mapSubtrees x.2.1) = natFold (appendLevel index) init x.1.start.val)
  · rintro ⟨it, a, ci, cur, proof⟩ ⟨hk, hend, hci, hplen, hst⟩
    simp only at hk hend hci hplen hst
    unfold zkcash.merkle_tree.MerkleTree.append_loop.body
    by_cases hlt : it.start.val < 26
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it1, ho, hs1, he1⟩
      simp only [ho]
      step*
      rw [hzb, bind_tc_ok]
      step*
      have hk' : it.start.val < 26 := hlt
      by_cases hev : i1 = 0#usize
      · simp only [hev, ↓reduceIte]
        step as ⟨x1, hx1, hx2⟩
        obtain ⟨hh, hhv, hhF⟩ := hHashv cur zero_byte
        obtain ⟨y1, back1⟩ := x1
        simp only at hx2
        subst hx2
        step*
        have hs2 : s2 = ⟨[⟨cur.val, by scalar_tac⟩, ⟨zero_byte.val, by scalar_tac⟩], by scalar_tac⟩ := by
          rw [s2_post, s_post, s1_post]; rfl
        rw [hs2, hhv, bind_tc_ok]
        simp only [core.result.Result.unwrap, bind_tc_ok]
        step*
        have hbit : Nat.testBit index it.start.val = false := by
          rw [Nat.testBit_eq_decide_div_mod_eq, ← hci]
          have : i1.val = 0 := by rw [hev]; rfl
          simp [← i1_post, this]
        have hzero : mapBytesToF zero_byte = LeanSpec.Z it.start.val := by
          have := hZ ⟨it.start.val, hk'⟩
          rw [getElem!_pos _ _ (by simp; omega)] at this
          rw [zero_byte_post]; exact this
        refine ⟨by omega, by rw [he1]; exact hend, ?_, by simp [hplen], ?_, by omega⟩
        · rw [current_index1_post, hci, hs1, Nat.div_div_eq_div_mul, pow_succ]
        · rw [hs1, natFold, ← hst, subtree_post2, mapSubtreesSet _ _ _ hk']
          simp only [appendLevel, dif_pos hk', hbit, Bool.false_eq_true, ↓reduceIte, hhF, hzero]
      · -- odd index bit: hash `(subtree, current)`, subtrees unchanged
        simp only [hev, ↓reduceIte]
        step as ⟨x1, hx1, hx2⟩
        obtain ⟨hh, hhv, hhF⟩ := hHashv subtree cur
        obtain ⟨y1, back1⟩ := x1
        simp only at hx2
        subst hx2
        step*
        have hs2 : s2 = ⟨[⟨subtree.val, by scalar_tac⟩, ⟨cur.val, by scalar_tac⟩], by scalar_tac⟩ := by
          rw [s2_post, s_post, s1_post]; rfl
        rw [hs2, hhv, bind_tc_ok]
        simp only [core.result.Result.unwrap, bind_tc_ok]
        step*
        have hbit : Nat.testBit index it.start.val = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq, ← hci]
          have : i1.val ≠ 0 := fun h0 => hev (by scalar_tac)
          have : i1.val < 2 := by rw [i1_post]; omega
          simp only [decide_eq_true_eq, ← i1_post]; omega
        have hsub : mapBytesToF subtree = mapSubtrees a ⟨it.start.val, hk'⟩ := by
          simp only [mapSubtrees, subtree_post1]
          rw [getElem!_pos _ _ (by simp; omega)]
        refine ⟨by omega, by rw [he1]; exact hend, ?_, by simp [hplen], ?_, by omega⟩
        · rw [current_index1_post, hci, hs1, Nat.div_div_eq_div_mul, pow_succ]
        · rw [hs1, natFold, ← hst, subtree_post2, mapSubtreesSet _ _ _ hk', hhF, hsub,
            Function.update_eq_self]
          simp only [appendLevel, dif_pos hk', hbit, ↓reduceIte]
    · -- all 26 levels done: the iterator is exhausted and the loop returns
      step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it1, ho, hit⟩
      simp only [ho]
      have h26 : it.start.val = 26 := by omega
      simp only [WP.spec_ok]
      rw [h26] at hst; exact hst
  · exact ⟨hk, hend, hci, hplen, hst⟩

theorem mapHistSet (a : Array (Array Std.U8 32#usize) 100#usize) (i : Std.Usize)
    (v : Array Std.U8 32#usize) (hi : i.val < 100) :
    (fun j : Fin 100 => mapBytesToF (a.set i v).val[j.val]!)
      = Function.update (fun j : Fin 100 => mapBytesToF a.val[j.val]!) ⟨i.val, hi⟩
          (mapBytesToF v) := by
  funext j
  have hlen : a.val.length = 100 := by simp
  by_cases hj : j = ⟨i.val, hi⟩
  · subst hj
    simp only [Function.update_self, Array.set_val_eq]
    rw [getElem!_pos _ _ (by simpa [hlen] using hi)]
    simp
  · have hj' : j.val ≠ i.val := fun h => hj (Fin.ext h)
    simp only [Function.update_of_ne hj, Array.set_val_eq]
    rw [getElem!_pos _ _ (by simp [hlen]), getElem!_pos _ _ (by simp [hlen])]
    simp [Ne.symm hj']

/-- Safety form of `appendRefines`: if `append` returns, the new account maps to
`appendEffects`. No room hypothesis: the code's own guard passing is all that's assumed.
`hHashv`/`hZeroBytes` tie the Poseidon axioms to the spec's hashes, as in `appendRefines`.
The 26-level loop is `appendLoopSpec`; the rest is the root-history bookkeeping. -/
theorem appendSafe [LeanSpec.PoseidonHashes]
    (leaf : Array Std.U8 32#usize) (ta ta' : zkcash.MerkleTreeAccount)
    (p : alloc.vec.Vec (Array Std.U8 32#usize))
    (hheight : ta.height.val = 26) (hsize : ta.root_history_size.val = 100)
    (hidx : ta.root_index.val < 100)
    (hHashv : ∀ a b : Array Std.U8 32#usize, ∃ h : Array Std.U8 32#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.hashv
          ⟨[⟨a.val, by scalar_tac⟩, ⟨b.val, by scalar_tac⟩], by scalar_tac⟩
        = ok (core.result.Result.Ok h) ∧
        mapBytesToF h = LeanSpec.PoseidonHashes.H2 (mapBytesToF a) (mapBytesToF b))
    (hZeroBytes : ∃ zeroBytes : Array (Array Std.U8 32#usize) 41#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.zero_bytes = ok zeroBytes ∧
      ∀ i : Fin 26, mapBytesToF (zeroBytes.val[i.val]!) = LeanSpec.Z i.val)
    (h : zkcash.merkle_tree.MerkleTree.append
        zkcash.light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher leaf ta
      = ok (.Ok p, ta')) :
    mapTree ta' = LeanSpec.appendEffects (mapBytesToF leaf) (mapTree ta) := by
  obtain ⟨zeroBytes, hzb, hZ⟩ := hZeroBytes
  unfold zkcash.merkle_tree.MerkleTree.append at h
  simp only [lift, bind_tc_ok] at h
  have hhu : (UScalar.cast .Usize ta.height).val = 26 := by simp [hheight]
  have hsu : (UScalar.cast .Usize ta.root_history_size).val = 100 := by simp [hsize]
  obtain ⟨mc, hmc, hmcv⟩ : ∃ mc, (1#u64 <<< UScalar.cast .Usize ta.height) = ok mc ∧
      mc.val = 2 ^ 26 := by
    have hs := U64.ShiftLeft_spec 1#u64 (UScalar.cast .Usize ta.height) (by rw [hhu]; decide)
    cases hc : (1#u64 <<< UScalar.cast .Usize ta.height) with
    | ok mc => rw [hc] at hs; refine ⟨mc, rfl, ?_⟩; have := hs.1; rw [hhu] at this; simp at this; rw [this]; simp [U64.size, U64.numBits]
    | fail e => rw [hc] at hs; simp at hs
    | div => rw [hc] at hs; simp at hs
  rw [hmc, bind_tc_ok] at h
  split_ifs at h with hroom
  swap; · reject h
  have hroomV : ta.next_index.val < 2 ^ 26 := by rw [← hmcv]; exact hroom
  have hciv : (UScalar.cast .Usize ta.next_index).val = ta.next_index.val := by
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    have : 2 ^ 26 ≤ 2 ^ UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by norm_num)
      (by cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits])
    omega
  peel h as pr hpr
  peel h as lp hlp
  obtain ⟨a1, hroot, proof1⟩ := lp
  unwrap h : ta.next_index.checked_add 1#u64 as val hval
  unwrap h : Usize.checked_add (UScalar.cast UScalarTy.Usize ta.root_index) 1#usize as val1 hval1
  peel h as nri hnri
  peel h as a2 ha2
  simp only [ok.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  -- the loop: 26 levels of `appendEffects`'s fold
  have hloop := appendLoopSpec ta.next_index.val (mapBytesToF leaf, mapSubtrees ta.subtrees)
    hHashv zeroBytes hzb hZ { start := 0#usize, «end» := UScalar.cast .Usize ta.height }
    ta.subtrees (UScalar.cast .Usize ta.next_index) leaf pr (by simp) hhu (by simp [hciv])
    (by rw [fromElemLen _ _ hpr, hhu]) rfl
  rw [hlp] at hloop
  have hpost := (WP.spec_ok _).mp hloop
  simp only at hpost
  -- the bookkeeping after the loop
  have hv := u64AddVal hval
  have hriu : (UScalar.cast .Usize ta.root_index).val = ta.root_index.val := by
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    have : 2 ^ 26 ≤ 2 ^ UScalarTy.Usize.numBits := Nat.pow_le_pow_right (by norm_num)
      (by cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits])
    omega
  have hv1 : val1.val = ta.root_index.val + 1 := by
    have hs := Usize.checked_add_bv_spec (UScalar.cast .Usize ta.root_index) 1#usize
    rw [hval1] at hs; rw [hs.2.1, hriu]; rfl
  have hnriv : nri.val = (ta.root_index.val + 1) % 100 := by
    rw [usizeRemVal (by rw [hsu]; norm_num) hnri, hv1, hsu]
  have hnri100 : nri.val < 100 := by rw [hnriv]; exact Nat.mod_lt _ (by norm_num)
  have ha2v : a2 = ta.root_history.set nri hroot := by
    have hs := Array.update_spec ta.root_history nri hroot (by simp; omega)
    rw [ha2] at hs; exact (WP.spec_ok _).mp hs
  have hidxF : (⟨nri.val, hnri100⟩ : Fin 100) = (mapTree ta).rootIndex + 1 := by
    apply Fin.ext
    simp only [mapTree, Fin.val_add, hnriv]
    rw [Nat.mod_eq_of_lt hidx]; rfl
  rw [appendEffectsFold]
  have hinit : ((mapBytesToF leaf, (mapTree ta).subtrees) : F × (Fin 26 → F))
      = (mapBytesToF leaf, mapSubtrees ta.subtrees) := rfl
  rw [hinit, show (mapTree ta).nextIndex = ta.next_index.val from rfl, ← hpost]
  simp only [mapTree]
  congr 1
  · rw [ha2v, mapHistSet _ _ _ hnri100, hidxF]; rfl
  · apply Fin.ext
    simp only [Fin.val_add]
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq _ _ (by simp; omega), hnriv,
      Nat.mod_eq_of_lt hidx]
    simp

/-- The spec-level `World` after a successful `fv_transact_entry` call.

* `tree`, `solBalance`, `config`: read off the code's returned accounts.
* `nullifiers`: the old set plus the two input nullifiers. The code model has no output for
  this: the real program records a spent nullifier by `init`-ing a PDA for it, an Anchor
  account-layer effect. Writing it here is that runtime behaviour, assumed, not derived.
* `balances`: the old balances, with the signer, recipient and fee recipient overwritten by
  the code's returned lamports (in that order). -/
def mapNewWorld (inputs : LeanSpec.TxInputs) (old : LeanSpec.World)
    (tree_account' : zkcash.MerkleTreeAccount) (global_config : zkcash.GlobalConfig)
    (tree_token_lamports' signer_lamports' : Std.U64)
    (recipient' fee_recipient_account' : zkcash.FvAccount) : LeanSpec.World where
  state :=
    { tree := mapTree tree_account', nullifiers := old.state.nullifiers ∪ {inputs.k0, inputs.k1},
      solBalance := tree_token_lamports'.val,
      config := mapGlobalConfig global_config tree_account'.max_deposit_amount }
  balances :=
    Function.update
      (Function.update (Function.update old.balances inputs.s signer_lamports'.val)
        (mapPubkey recipient'.key) recipient'.lamports.val)
      (mapPubkey fee_recipient_account'.key) fee_recipient_account'.lamports.val
  rentExemptMin := old.rentExemptMin

/-- The tree-account fields every real account has (`initialize` sets them; `append`
preserves them). `transactSafe` needs them of its input and returns them of its output. -/
def TreeShape (ta : zkcash.MerkleTreeAccount) : Prop :=
  ta.height.val = 26 ∧ ta.root_history_size.val = 100 ∧ ta.root_index.val < 100

set_option maxHeartbeats 4000000 in
/-- **Safety of `fv_transact_entry`**: if the code accepts a transaction, the spec's
`transact` holds between the mapped old and new worlds, and the returned tree account is
still well-formed (`TreeShape`, needed to chain steps in `Reachable.lean`). See the
hypothesis groups below for exactly what is assumed rather than derived. -/
theorem transactSafe
    [LeanSpec.Sha] [LeanSpec.PoseidonHashes]
    [AddCommGroup LeanSpec.G1] [Module F LeanSpec.G1] [AddCommGroup LeanSpec.G2]
    [Module F LeanSpec.G2] [CommGroup LeanSpec.GT] [LeanSpec.Pairing] [LeanSpec.Deployment]
    (tree_account : zkcash.MerkleTreeAccount) (global_config : zkcash.GlobalConfig)
    (proof_root proof_ext_data_hash proof_public_amount : Array Std.U8 32#usize)
    (input_nullifiers output_commitments : Array (Array Std.U8 32#usize) 2#usize)
    (proof_a : Array Std.U8 64#usize) (proof_b : Array Std.U8 128#usize)
    (proof_c : Array Std.U8 64#usize) (ext_data_minified : zkcash.ExtDataMinified)
    (encrypted_output1 encrypted_output2 : alloc.vec.Vec Std.U8)
    (rent_exempt_minimum tree_token_lamports signer_lamports : Std.U64)
    (recipient fee_recipient_account : zkcash.FvAccount)
    (ext_data : zkcash.ExtData)
    (s : LeanSpec.Pubkey) (π : LeanSpec.Groth16.Proof) (nullifiers : Finset F)
    (balances : LeanSpec.Pubkey → ℕ)
    -- What the code returned.
    (tree_account' : zkcash.MerkleTreeAccount)
    (tree_token_lamports' signer_lamports' : Std.U64)
    (recipient' fee_recipient_account' : zkcash.FvAccount)
    (h : zkcash.fv_transact_entry tree_account global_config proof_root proof_ext_data_hash
          proof_public_amount input_nullifiers output_commitments proof_a proof_b proof_c
          ext_data_minified encrypted_output1 encrypted_output2 rent_exempt_minimum
          tree_token_lamports signer_lamports recipient fee_recipient_account
        = ok (.Ok (), tree_account', tree_token_lamports', signer_lamports', recipient',
            fee_recipient_account'))
    (hextdata : zkcash.fv_ext_data_from_minified recipient fee_recipient_account
        ext_data_minified = ok ext_data)
    -- (1) How the old world's balances relate to the accounts the code is given.
    (hbalS : balances s = signer_lamports.val)
    (hbalA : balances (mapPubkey recipient.key) = recipient.lamports.val)
    (hbalT : balances (mapPubkey fee_recipient_account.key) = fee_recipient_account.lamports.val)
    -- (2) Account model. `fv_transact_entry` takes the recipient and fee recipient as two
    -- separate values, so it cannot express both being the same account (on-chain they would
    -- alias and receive both payouts). Out of scope here, so assumed away.
    (hAT : mapPubkey recipient.key ≠ mapPubkey fee_recipient_account.key)
    -- (3) Runtime: enforced outside the code model, by Anchor `init`-ing a PDA per nullifier
    -- (fails if it already exists). `nullifiersDistinct` needs no hypothesis: it follows from
    -- `proofValid` via `Deployment.soundness` (the circuit's `noDuplicateNullifiers`).
    (hFresh : LeanSpec.nullifiersFresh nullifiers (mapBytesToF input_nullifiers.val[0]!)
        (mapBytesToF input_nullifiers.val[1]!))
    -- (4) Verifier soundness: the Groth16 bridge (`proofValid` ↔ `fv_verify_proof_full_entry`)
    -- is not built yet, so the code's verifier accepting is assumed to mean `proofValid`.
    (hVerifySound : ∀ a a1 a2 a3 a4,
        curve_shim.FV_VK_ALPHA_G1 = ok a → curve_shim.FV_VK_BETA_G2 = ok a1 →
        curve_shim.FV_VK_GAMME_G2 = ok a2 → curve_shim.FV_VK_DELTA_G2 = ok a3 →
        curve_shim.FV_VK_IC = ok a4 →
        zkcash.utils.fv_verify_proof_full_entry proof_root proof_public_amount
          proof_ext_data_hash input_nullifiers output_commitments proof_a proof_b proof_c
          a a1 a2 a3 a4 = ok true →
        LeanSpec.proofValid (mapTxInputs s π proof_root proof_ext_data_hash proof_public_amount
          input_nullifiers output_commitments ext_data encrypted_output1 encrypted_output2))
    -- (5) Hash agreement: the code's SHA-256 / Poseidon axioms compute the spec's hashes.
    (hSha : ∀ (bytes : List Std.U8) (h : bytes.length ≤ Std.Usize.max),
      ∃ digest : Array Std.U8 32#usize,
        solana_sha256_hasher.hash ⟨bytes, h⟩ = ok digest ∧
        mapBytesToByteList digest.val = LeanSpec.Sha.sha256 (mapBytesToByteList bytes))
    (hHashv : ∀ a b : Array Std.U8 32#usize, ∃ h : Array Std.U8 32#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.hashv
          ⟨[⟨a.val, by scalar_tac⟩, ⟨b.val, by scalar_tac⟩], by scalar_tac⟩
        = ok (core.result.Result.Ok h) ∧
        mapBytesToF h = LeanSpec.PoseidonHashes.H2 (mapBytesToF a) (mapBytesToF b))
    (hZeroBytes : ∃ zeroBytes : Array (Array Std.U8 32#usize) 41#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.zero_bytes = ok zeroBytes ∧
      ∀ i : Fin 26, mapBytesToF (zeroBytes.val[i.val]!) = LeanSpec.Z i.val)
    (hExtDataSum : 32 + 8 + (4 + (alloc.vec.Vec.deref encrypted_output1).length)
        + (4 + (alloc.vec.Vec.deref encrypted_output2).length) + 8 + 32 + 32 ≤ Std.Usize.max)
    -- (6) Invariants of every real `GlobalConfig` / tree account. Discharged for
    -- code-reachable states by `CodeInv` in `Reachable.lean` (except `hRootCanon`).
    (hdrate : global_config.deposit_fee_rate.val ≤ 10000)
    (hwrate : global_config.withdrawal_fee_rate.val ≤ 10000)
    (hmrate : global_config.fee_error_margin.val ≤ 10000)
    -- `proof_root` is a canonical field element. The verifier itself rejects non-canonical
    -- public inputs (`fr_lt_modulus_be`), so this is derivable from `hb3`; not done yet.
    (hRootCanon : canonical proof_root)
    (hHistSize : tree_account.root_history_size.val = 100)
    (hRootIdx : tree_account.root_index.val < 100)
    (hheight : tree_account.height.val = 26)
    -- (7) CODE DEVIATIONS from the spec. The code accepts some transactions the spec rejects;
    -- these are exactly the extra conditions the spec imposes and the code doesn't check.
    -- (a) Deposit with a fee: the code checks the pool balance *after* the deposit
    --     (`pool + extAmt ≥ fee + rent`, lib.rs:697); the spec's `poolSolvent` checks it before.
    (hDevPool : ext_data.ext_amount.val > 0 → ext_data.fee.val > 0 →
        tree_token_lamports.val ≥ ext_data.fee.val + rent_exempt_minimum.val)
    -- (b) Tree room: the code accepts `next_index ≤ 2^26 - 2` (both appends fit); the spec's
    --     `treeHasRoom` stops one leaf earlier.
    (hDevRoom : tree_account.next_index.val < 2 ^ 26 - 2) :
    let inputs := mapTxInputs s π proof_root proof_ext_data_hash proof_public_amount
      input_nullifiers output_commitments ext_data encrypted_output1 encrypted_output2
    let oldWorld := mapOldWorld tree_account global_config nullifiers balances
      tree_token_lamports rent_exempt_minimum
    LeanSpec.transact inputs oldWorld
      (mapNewWorld inputs oldWorld tree_account' global_config tree_token_lamports'
        signer_lamports' recipient' fee_recipient_account') ∧
    TreeShape tree_account' := by
  intro inputs oldWorld
  unfold zkcash.fv_transact_entry at h
  rw [hextdata, bind_tc_ok] at h
  -- `is_known_root`
  peel h as b hb
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; reject h
  simp only [↓reduceIte] at h
  -- ext-data hash, then its comparison against the proof's public input
  peel h as r hr
  peel h as cf hcf
  rcases branchOkInv hcf with ⟨extHash, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  swap; · reject h
  peel h as fs hfs
  peel h as fs1 hfs1
  peel h as b1 hb1
  cases b1
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; reject h
  simp only [↓reduceIte] at h
  -- `check_public_amount`
  peel h as b2 hb2
  cases b2
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; reject h
  simp only [↓reduceIte] at h
  -- `validate_fee`
  peel h as r1 hr1
  peel h as cf1 hcf1
  rcases branchOkInv hcf1 with ⟨u, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
  swap; · reject h
  -- the verifying key and the proof
  peel h as a ha
  peel h as a1 ha1
  peel h as a2 ha2
  peel h as a3 ha3
  peel h as a4 ha4
  peel h as b3 hb3
  cases b3
  · simp only [Bool.false_eq_true, ↓reduceIte] at h; reject h
  simp only [↓reduceIte] at h
  ------------------------------------------------------------------------------------------
  -- Preconditions every accepted transaction satisfies, whatever its direction.
  ------------------------------------------------------------------------------------------
  have hRoot : LeanSpec.rootKnown (mapTree tree_account) (mapBytesToF proof_root) := by
    have hs := isKnownRootSafe tree_account proof_root hRootCanon hHistSize hRootIdx
    rw [hb] at hs
    exact (WP.spec_ok _).mp hs rfl
  have hPubAmt : LeanSpec.pubAmtConsistent ext_data.ext_amount.val ext_data.fee.val
      (mapBytesToF proof_public_amount) := by
    have hs := checkPublicAmountRefines ext_data.ext_amount ext_data.fee proof_public_amount
    rw [hb2] at hs
    exact ((WP.spec_ok _).mp hs).mp rfl
  have hFee : LeanSpec.feeSufficient (mapGlobalConfig global_config
      tree_account.max_deposit_amount) ext_data.ext_amount.val ext_data.fee.val := by
    have hf := feeSufficientRefines ext_data.ext_amount ext_data.fee
      global_config.deposit_fee_rate global_config.withdrawal_fee_rate
      global_config.fee_error_margin hdrate hwrate hmrate hr1
    simpa only [LeanSpec.feeSufficient, mapGlobalConfig] using hf
  have hExt : LeanSpec.externalDataBound inputs := by
    have hs := externalDataBoundRefines ext_data.recipient ext_data.fee_recipient
      ext_data.mint_address ext_data.ext_amount (alloc.vec.Vec.deref encrypted_output1)
      (alloc.vec.Vec.deref encrypted_output2) ext_data.fee hSha hExtDataSum
    rw [hr] at hs
    obtain ⟨hh, hhEq, hhVal⟩ := (WP.spec_ok _).mp hs
    cases hhEq
    -- the code's field comparison: `from_le(hash) = from_be(proof's public input)` in 𝔽ᵣ
    have hfsv : fs = (mapBytesToNatLE extHash : fr_shim.FrShim) := by
      unfold fr_shim.FrShim.from_le_bytes_mod_order at hfs
      unfold mapBytesToNatLE; exact (ok.inj hfs).symm
    have hfs1v : fs1 = (mapBytesToNat proof_ext_data_hash : fr_shim.FrShim) := by
      unfold fr_shim.FrShim.from_be_bytes_mod_order at hfs1
      unfold mapBytesToNat; exact (ok.inj hfs1).symm
    have hfeq : fs = fs1 := by
      unfold fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq at hb1
      simpa using hb1
    rw [hfsv, hfs1v] at hfeq
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hfeq
    rw [← hp_eq_bn254r] at hmod
    have hF : (mapBytesToNatLE extHash : F) = mapBytesToF proof_ext_data_hash :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
    show LeanSpec.externalDataHash inputs = mapBytesToF proof_ext_data_hash
    rw [← externalDataHashOfEq, ← hF, hhVal]
    rfl
  have hProof : LeanSpec.proofValid inputs := hVerifySound a a1 a2 a3 a4 ha ha1 ha2 ha3 ha4 hb3
  have hDistinct : LeanSpec.nullifiersDistinct inputs.k0 inputs.k1 := by
    obtain ⟨w, hw⟩ := LeanSpec.Deployment.soundness _ _ hProof
    exact hw.noDuplicateNullifiers
  -- `ext_data` is the minified input plus the two account keys and the SOL mint.
  have hRecKey : ext_data.recipient = recipient.key := by
    unfold zkcash.fv_ext_data_from_minified at hextdata
    obtain ⟨_, _, hextdata⟩ := bindOkInv hextdata
    rw [← (ok.inj hextdata)]
  have hFeeKey : ext_data.fee_recipient = fee_recipient_account.key := by
    unfold zkcash.fv_ext_data_from_minified at hextdata
    obtain ⟨_, _, hextdata⟩ := bindOkInv hextdata
    rw [← (ok.inj hextdata)]
  by_cases hpos : ext_data.ext_amount > 0#i64
  · ----------------------------------------------------------------------------------------
    -- Deposit.
    ----------------------------------------------------------------------------------------
    rw [if_pos hpos] at h
    simp only [lift, bind_tc_ok] at h
    have hposV : ext_data.ext_amount.val > 0 := by scalar_tac
    have hcast : (IScalar.hcast .U64 ext_data.ext_amount : Std.U64).val
        = ext_data.ext_amount.val := IScalar.hcast_inBounds_spec .U64 ext_data.ext_amount
      (by scalar_tac)
    by_cases hlim : IScalar.hcast .U64 ext_data.ext_amount ≤ tree_account.max_deposit_amount
    swap; · rw [if_neg hlim] at h; reject h
    rw [if_pos hlim] at h
    unwrap h : signer_lamports.checked_sub (IScalar.hcast .U64 ext_data.ext_amount) as val1 hval1
    unwrap h : tree_token_lamports.checked_add (IScalar.hcast .U64 ext_data.ext_amount)
      as val2 hval2
    have hge0 : ext_data.ext_amount ≥ 0#i64 := by scalar_tac
    by_cases hfee : ext_data.fee > 0#u64
    · rw [if_pos hfee, if_pos hge0] at h
      unwrap h : ext_data.fee.checked_add rent_exempt_minimum as val3 hval3
      by_cases hg : val2 ≥ val3
      swap; · rw [if_neg hg] at h; reject h
      rw [if_pos hg] at h
      unwrap h : val2.checked_sub ext_data.fee as val4 hval4
      unwrap h : fee_recipient_account.lamports.checked_add ext_data.fee as val5 hval5
      peel h as c0 hc0
      peel h as p0 hp0
      obtain ⟨r7, ta1⟩ := p0
      peel h as cf7 hcf7
      rcases branchOkInv hcf7 with ⟨_, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      swap; · reject h
      peel h as c1 hc1
      peel h as p1 hp1
      obtain ⟨r8, ta2⟩ := p1
      peel h as cf8 hcf8
      rcases branchOkInv hcf8 with ⟨_, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      swap; · reject h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := h
      have e1 := u64SubVal hval1
      have e2 := u64AddVal hval2
      have e3 := u64AddVal hval3
      have e4 := u64SubVal hval4
      have e5 := u64AddVal hval5
      have hgeV : val2.val ≥ val3.val := hg
      have hfeeV : ext_data.fee.val > 0 := by scalar_tac
      obtain ⟨hh1, hsz1, hm1, -, hidx1⟩ := appendStruct _ _ _ _ hp0
      obtain ⟨hh2, hsz2, hm2, -, hidx2⟩ := appendStruct _ _ _ _ hp1
      have ht1 := appendSafe c0 tree_account ta1 _ hheight hHistSize hRootIdx hHashv hZeroBytes hp0
      have ht2 := appendSafe c1 ta1 ta2 _ (by rw [hh1]; exact hheight)
        (by rw [hsz1]; exact hHistSize) (hidx1 hHistSize) hHashv hZeroBytes hp1
      have hc0' := indexOk _ _ _ hc0
      have hc1' := indexOk _ _ _ hc1
      have hne0 : ext_data.ext_amount.val ≠ 0 := by omega
      refine ⟨⟨⟨hRoot, hExt, hFee, hPubAmt, hProof, hFresh, hDistinct, ?_, ?_, ?_, hDevRoom⟩,
        ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · exact (depositWithinLimitRefines ext_data.ext_amount tree_account.max_deposit_amount
          _ rfl hposV).mp hlim
      · exact ⟨fun hn => absurd (show ext_data.ext_amount.val < 0 from hn) (by omega),
          fun ⟨_, hf⟩ => hDevPool hposV hf⟩
      · exact (signerSolventRefines ext_data.ext_amount signer_lamports balances s hbalS
          hposV).mp (by rw [hval1]; rfl)
      · show mapTree ta2 = (LeanSpec.transactEffects inputs oldWorld).state.tree
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects_tree]
        rw [ht2, ht1, hc0', hc1']
        rfl
      · simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects]
        split_ifs <;> rfl
      · show val4.val = (LeanSpec.transactEffects inputs oldWorld).state.solBalance
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld,
          mapTxInputs, mapOldWorld, if_neg hne0, if_pos hposV]
        omega
      · show mapGlobalConfig global_config ta2.max_deposit_amount
          = (LeanSpec.transactEffects inputs oldWorld).state.config
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld,
          mapTxInputs, mapOldWorld, if_neg hne0, if_pos hposV, hm2, hm1]
      · simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects]
        split_ifs <;> rfl
      · intro k hk hks
        simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects, inputs,
          oldWorld, mapTxInputs, mapOldWorld, if_neg hne0, if_pos hposV, hRecKey,
          hFeeKey] at hk hks ⊢
        rcases hk with rfl | rfl
        · simp [Function.update_of_ne hAT, Function.update_of_ne hks, hbalA]
        · simp [Function.update_of_ne hks, hbalT, e5]
      · exact ⟨by rw [hh2, hh1]; exact hheight, by rw [hsz2, hsz1]; exact hHistSize,
          hidx2 (by rw [hsz1]; exact hHistSize)⟩
    · -- deposit, no fee: the two appends follow directly
      rw [if_neg hfee] at h
      have hfee0 : ext_data.fee.val = 0 := by
        have : ¬ ext_data.fee.val > 0 := hfee
        omega
      peel h as c0 hc0
      peel h as p0 hp0
      obtain ⟨r7, ta1⟩ := p0
      peel h as cf7 hcf7
      rcases branchOkInv hcf7 with ⟨_, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      swap; · reject h
      peel h as c1 hc1
      peel h as p1 hp1
      obtain ⟨r8, ta2⟩ := p1
      peel h as cf8 hcf8
      rcases branchOkInv hcf8 with ⟨_, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      swap; · reject h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := h
      have e1 := u64SubVal hval1
      have e2 := u64AddVal hval2
      obtain ⟨hh1, hsz1, hm1, -, hidx1⟩ := appendStruct _ _ _ _ hp0
      obtain ⟨hh2, hsz2, hm2, -, hidx2⟩ := appendStruct _ _ _ _ hp1
      have ht1 := appendSafe c0 tree_account ta1 _ hheight hHistSize hRootIdx hHashv hZeroBytes hp0
      have ht2 := appendSafe c1 ta1 ta2 _ (by rw [hh1]; exact hheight)
        (by rw [hsz1]; exact hHistSize) (hidx1 hHistSize) hHashv hZeroBytes hp1
      have hc0' := indexOk _ _ _ hc0
      have hc1' := indexOk _ _ _ hc1
      have hne0 : ext_data.ext_amount.val ≠ 0 := by omega
      refine ⟨⟨⟨hRoot, hExt, hFee, hPubAmt, hProof, hFresh, hDistinct, ?_, ?_, ?_, hDevRoom⟩,
        ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · exact (depositWithinLimitRefines ext_data.ext_amount tree_account.max_deposit_amount
          _ rfl hposV).mp hlim
      · exact ⟨fun hn => absurd (show ext_data.ext_amount.val < 0 from hn) (by omega),
          fun ⟨_, hf⟩ => absurd (show ext_data.fee.val > 0 from hf) (by omega)⟩
      · exact (signerSolventRefines ext_data.ext_amount signer_lamports balances s hbalS
          hposV).mp (by rw [hval1]; rfl)
      · show mapTree ta2 = (LeanSpec.transactEffects inputs oldWorld).state.tree
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects_tree]
        rw [ht2, ht1, hc0', hc1']
        rfl
      · simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects]
        split_ifs <;> rfl
      · show val2.val = (LeanSpec.transactEffects inputs oldWorld).state.solBalance
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld,
          mapTxInputs, mapOldWorld, if_neg hne0, if_pos hposV]
        omega
      · show mapGlobalConfig global_config ta2.max_deposit_amount
          = (LeanSpec.transactEffects inputs oldWorld).state.config
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld,
          mapTxInputs, mapOldWorld, if_neg hne0, if_pos hposV, hm2, hm1]
      · simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects]
        split_ifs <;> rfl
      · intro k hk hks
        simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects, inputs,
          oldWorld, mapTxInputs, mapOldWorld, if_neg hne0, if_pos hposV, hRecKey,
          hFeeKey] at hk hks ⊢
        rcases hk with rfl | rfl
        · simp [Function.update_of_ne hAT, Function.update_of_ne hks, hbalA]
        · simp [Function.update_of_ne hks, hbalT, hfee0]
      · exact ⟨by rw [hh2, hh1]; exact hheight, by rw [hsz2, hsz1]; exact hHistSize,
          hidx2 (by rw [hsz1]; exact hHistSize)⟩
  · rw [if_neg hpos] at h
    have hnpos : ¬ ext_data.ext_amount.val > 0 := by scalar_tac
    by_cases hneg : ext_data.ext_amount < 0#i64
    swap
    · -- `ext_amount = 0` never gets this far: `pubAmtConsistent` (checked above) rules it out.
      exfalso
      have h0 : ext_data.ext_amount.val = 0 := by scalar_tac
      have := hPubAmt.2.1 (by omega)
      omega
    --------------------------------------------------------------------------------------
    -- Withdrawal.
    --------------------------------------------------------------------------------------
    rw [if_pos hneg] at h
    have hnegV : ext_data.ext_amount.val < 0 := by scalar_tac
    have hmin : ext_data.ext_amount ≠ core.num.I64.MIN := by
      intro hc; apply hPubAmt.1; rw [hc]; simp [I64.rMin]
    obtain ⟨y, hy, hyv⟩ : ∃ y : Std.I64, IScalar.neg ext_data.ext_amount = ok y ∧
        y.val = -ext_data.ext_amount.val := by
      have hs := IScalar.neg_step ext_data.ext_amount
        (by intro hc; apply hmin; apply IScalar.eq_of_val_eq; rw [hc]; simp [I64.min_eq, I64.rMin])
      cases hc : IScalar.neg ext_data.ext_amount with
      | ok y => rw [hc] at hs; exact ⟨y, rfl, by simpa using hs⟩
      | fail e => rw [hc] at hs; simp at hs
      | div => rw [hc] at hs; simp at hs
    have hy0 : 0 ≤ y.val := by omega
    simp only [core.num.I64.checked_neg, if_neg hmin, hy, bind_tc_ok, core.option.Option.ok_or,
      core.result.Result.Insts.CoreOpsTry.branch,
      U64.Insts.CoreConvertTryFromI64TryFromIntError.try_from, if_pos hy0,
      core.result.Result.map_err, lift] at h
    have hwa : (IScalar.hcast .U64 y : Std.U64).val = ext_data.ext_amount.val.natAbs := by
      have := IScalar.hcast_inBounds_spec .U64 y (by scalar_tac)
      simp only [lift, WP.spec_ok] at this
      omega
    unwrap h : U64.checked_add (IScalar.hcast .U64 y) ext_data.fee as val3 hval3
    unwrap h : val3.checked_add rent_exempt_minimum as val4 hval4
    by_cases hg : tree_token_lamports ≥ val4
    swap; · rw [if_neg hg] at h; reject h
    rw [if_pos hg] at h
    unwrap h : U64.checked_sub tree_token_lamports (IScalar.hcast .U64 y) as val5 hval5
    unwrap h : U64.checked_add recipient.lamports (IScalar.hcast .U64 y) as val6 hval6
    by_cases hfee : ext_data.fee > 0#u64
    · -- withdrawal with a fee
      rw [if_pos hfee, if_neg (by scalar_tac : ¬ ext_data.ext_amount ≥ 0#i64)] at h
      unwrap h : U64.checked_sub val5 ext_data.fee as val7 hval7
      unwrap h : U64.checked_add fee_recipient_account.lamports ext_data.fee as val8 hval8
      have e7 := u64SubVal hval7
      have e8 := u64AddVal hval8
      peel h as c0 hc0
      peel h as p0 hp0
      obtain ⟨r7, ta1⟩ := p0
      peel h as cf7 hcf7
      rcases branchOkInv hcf7 with ⟨_, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      swap; · reject h
      peel h as c1 hc1
      peel h as p1 hp1
      obtain ⟨r8, ta2⟩ := p1
      peel h as cf8 hcf8
      rcases branchOkInv hcf8 with ⟨_, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      swap; · reject h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := h
      have e3 := u64AddVal hval3
      have e4 := u64AddVal hval4
      have e5 := u64SubVal hval5
      have e6 := u64AddVal hval6
      have hgV : tree_token_lamports.val ≥ val4.val := hg
      obtain ⟨hh1, hsz1, hm1, -, hidx1⟩ := appendStruct _ _ _ _ hp0
      obtain ⟨hh2, hsz2, hm2, -, hidx2⟩ := appendStruct _ _ _ _ hp1
      have ht1 := appendSafe c0 tree_account ta1 _ hheight hHistSize hRootIdx hHashv hZeroBytes hp0
      have ht2 := appendSafe c1 ta1 ta2 _ (by rw [hh1]; exact hheight)
        (by rw [hsz1]; exact hHistSize) (hidx1 hHistSize) hHashv hZeroBytes hp1
      have hc0' := indexOk _ _ _ hc0
      have hc1' := indexOk _ _ _ hc1
      have hne0 : ext_data.ext_amount.val ≠ 0 := by omega
      have habs : (ext_data.ext_amount.val.natAbs : ℤ) = -ext_data.ext_amount.val := by omega
      refine ⟨⟨⟨hRoot, hExt, hFee, hPubAmt, hProof, hFresh, hDistinct, ?_, ?_, ?_, hDevRoom⟩,
        ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · exact fun hp => absurd (show ext_data.ext_amount.val > 0 from hp) hnpos
      · refine ⟨fun _ => ?_, fun ⟨hge, _⟩ => absurd (show ext_data.ext_amount.val ≥ 0 from hge)
          (by omega)⟩
        show (tree_token_lamports.val : ℤ) ≥ |ext_data.ext_amount.val| + ext_data.fee.val
          + rent_exempt_minimum.val
        rw [Int.abs_eq_natAbs]
        omega
      · exact fun hp => absurd (show ext_data.ext_amount.val > 0 from hp) hnpos
      · show mapTree ta2 = (LeanSpec.transactEffects inputs oldWorld).state.tree
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects_tree]
        rw [ht2, ht1, hc0', hc1']
        rfl
      · simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects]
        split_ifs <;> rfl
      · show val7.val = (LeanSpec.transactEffects inputs oldWorld).state.solBalance
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld,
          mapTxInputs, mapOldWorld, if_neg hne0, if_neg hnpos]
        omega
      · show mapGlobalConfig global_config ta2.max_deposit_amount
          = (LeanSpec.transactEffects inputs oldWorld).state.config
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld,
          mapTxInputs, mapOldWorld, if_neg hne0, if_neg hnpos, hm2, hm1]
      · simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects]
        split_ifs <;> rfl
      · intro k hk hks
        simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects, inputs,
          oldWorld, mapTxInputs, mapOldWorld, if_neg hne0, if_neg hnpos, hRecKey,
          hFeeKey] at hk hks ⊢
        rcases hk with rfl | rfl
        · simp [Function.update_of_ne hAT, hbalA, e6, hwa]
        · simp [Function.update_of_ne hAT.symm, hbalT, e8]
      · exact ⟨by rw [hh2, hh1]; exact hheight, by rw [hsz2, hsz1]; exact hHistSize,
          hidx2 (by rw [hsz1]; exact hHistSize)⟩
    · -- withdrawal, no fee
      rw [if_neg hfee] at h
      have hfee0 : ext_data.fee.val = 0 := by
        have : ¬ ext_data.fee.val > 0 := hfee
        omega
      peel h as c0 hc0
      peel h as p0 hp0
      obtain ⟨r7, ta1⟩ := p0
      peel h as cf7 hcf7
      rcases branchOkInv hcf7 with ⟨_, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      swap; · reject h
      peel h as c1 hc1
      peel h as p1 hp1
      obtain ⟨r8, ta2⟩ := p1
      peel h as cf8 hcf8
      rcases branchOkInv hcf8 with ⟨_, rfl, rfl⟩ | ⟨e, rfl, rfl⟩
      swap; · reject h
      simp only [ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, rfl, rfl, rfl, rfl⟩ := h
      have e3 := u64AddVal hval3
      have e4 := u64AddVal hval4
      have e5 := u64SubVal hval5
      have e6 := u64AddVal hval6
      have hgV : tree_token_lamports.val ≥ val4.val := hg
      obtain ⟨hh1, hsz1, hm1, -, hidx1⟩ := appendStruct _ _ _ _ hp0
      obtain ⟨hh2, hsz2, hm2, -, hidx2⟩ := appendStruct _ _ _ _ hp1
      have ht1 := appendSafe c0 tree_account ta1 _ hheight hHistSize hRootIdx hHashv hZeroBytes hp0
      have ht2 := appendSafe c1 ta1 ta2 _ (by rw [hh1]; exact hheight)
        (by rw [hsz1]; exact hHistSize) (hidx1 hHistSize) hHashv hZeroBytes hp1
      have hc0' := indexOk _ _ _ hc0
      have hc1' := indexOk _ _ _ hc1
      have hne0 : ext_data.ext_amount.val ≠ 0 := by omega
      have habs : (ext_data.ext_amount.val.natAbs : ℤ) = -ext_data.ext_amount.val := by omega
      refine ⟨⟨⟨hRoot, hExt, hFee, hPubAmt, hProof, hFresh, hDistinct, ?_, ?_, ?_, hDevRoom⟩,
        ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, ?_⟩
      · exact fun hp => absurd (show ext_data.ext_amount.val > 0 from hp) hnpos
      · refine ⟨fun _ => ?_, fun ⟨hge, _⟩ => absurd (show ext_data.ext_amount.val ≥ 0 from hge)
          (by omega)⟩
        show (tree_token_lamports.val : ℤ) ≥ |ext_data.ext_amount.val| + ext_data.fee.val
          + rent_exempt_minimum.val
        rw [Int.abs_eq_natAbs]
        omega
      · exact fun hp => absurd (show ext_data.ext_amount.val > 0 from hp) hnpos
      · show mapTree ta2 = (LeanSpec.transactEffects inputs oldWorld).state.tree
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects_tree]
        rw [ht2, ht1, hc0', hc1']
        rfl
      · simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects]
        split_ifs <;> rfl
      · show val5.val = (LeanSpec.transactEffects inputs oldWorld).state.solBalance
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld,
          mapTxInputs, mapOldWorld, if_neg hne0, if_neg hnpos]
        omega
      · show mapGlobalConfig global_config ta2.max_deposit_amount
          = (LeanSpec.transactEffects inputs oldWorld).state.config
        simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld,
          mapTxInputs, mapOldWorld, if_neg hne0, if_neg hnpos, hm2, hm1]
      · simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects]
        split_ifs <;> rfl
      · intro k hk hks
        simp only [mapNewWorld, LeanSpec.transactEffects, LeanSpec.transferEffects, inputs,
          oldWorld, mapTxInputs, mapOldWorld, if_neg hne0, if_neg hnpos, hRecKey,
          hFeeKey] at hk hks ⊢
        rcases hk with rfl | rfl
        · simp [Function.update_of_ne hAT, hbalA, e6, hwa]
        · simp [Function.update_of_ne hAT.symm, hbalT, hfee0]
      · exact ⟨by rw [hh2, hh1]; exact hheight, by rw [hsz2, hsz1]; exact hHistSize,
          hidx2 (by rw [hsz1]; exact hHistSize)⟩
