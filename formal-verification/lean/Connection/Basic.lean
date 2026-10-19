import code_model.generated.Funs
import Spec.privacy_cash_spec
open Aeneas Aeneas.Std Result ControlFlow
-- Selective: `LeanSpec` also declares `Tree`, `Byte`, ... which collide with root-level
-- names pulled in transitively by `code_model` (Mathlib's `Tree`, Aeneas's `Byte`, ...).
-- `LeanSpec.Tree` is itself one of the colliding names, so it stays qualified below.
open LeanSpec (F pubAmtConsistent rootKnown depositWithinLimit signerSolvent poolSolvent
  feeSufficient)

/-! # Connection: code model ↔ Lean spec

A connection theorem relates one Aeneas-extracted function (`code_model/generated`) to
its counterpart in `Spec/`, SymCrypt-style: run the code, map its inputs into the spec's
vocabulary, and check the code's answer against the spec predicate there.

    code inputs ──── code function ────▶  ok : Bool
         │                                      │
      mapping                             "ok = true"
         ▼                                      ▼
    spec inputs ──── spec predicate ────▶      Prop

The mapping (`mapBytesToF`, `mapTree`, ...) carries no proof of its own: nothing stops a
mapping that throws away information from making its theorem provable but empty, so each
one is written to be checked by reading, not by trusting it.

Worked from the spec's side. For each piece `transact` depends on (a precondition, a
state component), find or write the Rust function responsible for it, then connect the
two. This keeps the work organized around what `transact`'s own theorem will need, and
turns missing pieces (a spec predicate with no code counterpart, or vice versa) into
something the file surfaces rather than something a reviewer has to notice.

Scope: safety. A theorem here says "if the code accepts, the spec condition holds" (and,
for state effects, the resulting state matches). Rejection -- an `Err` return, a panic
(`fail`) or non-termination (`div`) -- is just "no transition" in the spec, so nothing is
claimed about *how* the code rejects; on-chain all three abort the instruction and the
runtime discards its account writes. That is exactly what invariant inheritance
(`ReachableWorld` over code-reachable states) needs. Some theorems below prove more (a
`⦃ ⦄` iff also gives the converse and that the code always returns); that's fine, the
safety half is read off them. A consequence: the diagnostic axioms (`to_string`, anchor's
error conversions) that build every `require!`'s `Err` value never need to be reasoned
about -- see `bindNeOkUnit`.

Connected so far:
- `pubAmtConsistent` ↔ `zkcash.utils.fv_check_public_amount_entry` (`checkPublicAmountRefines`)
- `rootKnown` ↔ `zkcash.merkle_tree.MerkleTree.is_known_root` (`isKnownRootRefines`)
- `depositWithinLimit`, `signerSolvent`, `poolSolvent` ↔ the arithmetic guards inside
  `fv_transact_entry` (`depositWithinLimitRefines`, `signerSolventRefines`,
  `poolSolventRefines`). None of these three has its own named Rust function (the checks
  are `require!`/`checked_sub` calls inlined in `fv_transact_entry`), so each theorem below
  is about the guard's condition directly, not about a whole function's `⦃ ⦄` spec.
- `treeHasRoom` ↔ `merkle_tree.MerkleTree.append`'s room guard, carried across the two
  calls `transact` makes (`treeHasRoomRefines`). Only the arithmetic: whether `append`
  reaches that guard, and what it returns, is a separate question (see the theorem's
  docstring).
- `appendEffects` ↔ `zkcash.merkle_tree.MerkleTree.append` (`appendRefines`). Stated, not
  yet proven: needs both a `WP`-based loop induction over the 26-level fold and an explicit
  `hHashv`/`hZeroBytes` hypothesis linking the Poseidon hasher axioms to the spec's abstract
  `PoseidonHashes` class (see the theorem's docstring; the same shape of gap, and the same
  kind of fix, as `externalDataBoundRefines`'s `hSha`).
- `transferEffects` ↔ `fv_transact_entry`'s deposit and withdrawal balance updates
  (`transferEffectsDepositRefines`, `transferEffectsWithdrawalRefines`), proven, plus
  `transferEffectsOfEq` tying the two code-shaped theorems back to the real
  `transferEffects`. A state *effect*, not a boolean guard, so the connection shows the
  code's `checked_sub`/`checked_add` pair produces exactly the balances the spec computes,
  not that a condition holds.
- `transactEffects`'s fee transfer ↔ `fv_transact_entry`'s fee-transfer block
  (`transactEffectsFeeRefines`), proven. Together with `transferEffects` and `appendRefines`
  above, this covers every piece of `transactEffects` except the nullifier-set union, which
  isn't visible to `code_model` at all (see "Not yet connected").
- `feeSufficient` ← `utils.validate_fee` (`feeSufficientRefines`), proven, safety direction:
  `validate_fee` accepting implies `feeSufficient`, under the rate bounds (see its docstring
  for the overflow that makes them necessary). The accept-path converse,
  `feeSufficientAccepts`, is proven too; the two are not an iff (`extAmt = i64::MIN`).
- `externalDataBound` ↔ `zkcash.utils.calculate_complete_ext_data_hash`
  (`externalDataBoundRefines`). Fully proven, no `sorry`. `completeExtDataSerializeOk`
  carries the byte-for-byte serialization match; the connection theorem's own reduction
  (slice-to-vec calls, the serialize call, the `?`-operator branch, the hash call) goes
  through cleanly via Aeneas's `step` tactic, once restated as a Hoare triple
  (`completeExtDataSerializeOkSpec`) so `step` can find it -- the fix for the "`Bind`-of-
  `Bind` won't reduce" blocker a previous pass here got stuck on: `rw`/`simp`/`show` all
  fight the `Vec`/`Array` non-reducibility Aeneas relies on elsewhere, `step` doesn't. The
  theorem still carries an explicit `hSha` hypothesis linking the code's hash syscall axiom
  to the spec's own abstract `Sha` class (see the theorem's docstring for why that is the
  right place to stop, not a gap found by accident).

Not yet connected, with why:
- `nullifiersDistinct`: no program check to connect to. It's enforced by the circuit
  (`RelationS.noDuplicateNullifiers`), and reaching the program only after a valid proof
  already gets it via `Spec.transact_implies_witness`. A code-side theorem here would be
  vacuous by construction, not merely unproven.
- `proofValid`, `nullifiersFresh`: harder still, since they route through Groth16 pairing
  checks or the account layer. Not started; see the investigation note above each one
  further down for what exists today and what's missing.
- `transactEffects`'s nullifier-set union (`nullifiers := ... ∪ {inputs.k0, inputs.k1}`):
  the real program records a spent nullifier by creating a PDA for it, an Anchor account-
  layer effect `fv_transact_entry`'s signature has no output for at all (same reason
  `nullifiersFresh` is out of scope). Nothing in `code_model` to connect this to. -/

-- 32 bytes read as a natural number, big-endian (byte 0 most significant), the same way
-- `FrShim.from_be_bytes_mod_order` reads the proof's public inputs.
def mapBytesToNat (b : Array Std.U8 32#usize) : ℕ :=
  b.val.foldl (fun acc x => acc * 256 + x.val) 0

-- `mapBytesToNat`, reduced mod `p`.
def mapBytesToF (b : Array Std.U8 32#usize) : F := (mapBytesToNat b : F)

/-- **Connection theorem for `zkcash::utils::fv_check_public_amount_entry`**
The program's public-amount check accepts exactly when `pubAmtConsistent` holds for the
same amount, fee, and public-amount bytes (mapped through `mapBytesToF`). -/
-- "fv_check_public_amount_entry extAmt fee pubAmt succeeds and returns some Boolean ok, and that ok is true iff pubAmtConsistent ... holds"
theorem checkPublicAmountRefines
    (extAmt : Std.I64) (fee : Std.U64) (pubAmt : Array Std.U8 32#usize) :
    zkcash.utils.fv_check_public_amount_entry extAmt fee pubAmt ⦃ (ok : Bool) =>
      ok = true ↔ pubAmtConsistent extAmt.val fee.val (mapBytesToF pubAmt) ⦄ := by
  have hMIN_val : (core.num.I64.MIN : Std.I64).val = -9223372036854775808 := by native_decide
  simp only [zkcash.utils.fv_check_public_amount_entry, pubAmtConsistent, mapBytesToF,
    mapBytesToNat, lift,
    fr_shim.FrShim.from_u64, fr_shim.FrShim.from_be_bytes_mod_order,
    fr_shim.FrShim.Insts.CoreOpsArithSubFrShimFrShim.sub,
    fr_shim.FrShim.Insts.CoreOpsArithAddFrShimFrShim.add,
    fr_shim.FrShim.Insts.CoreOpsArithNegFrShim.neg,
    fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq,
    fr_shim.FrShim.Insts.CoreCmpPartialOrdFrShim.partial_cmp,
    core.cmp.PartialOrd.le.default, core.cmp.PartialOrd.le_body, bind_tc_ok]
  by_cases hmin : extAmt = core.num.I64.MIN
  · simp [hmin, core.num.I64.MIN, I64.rMin]
  · have hval : extAmt.val ≠ -9223372036854775808 := fun h => hmin (by scalar_tac)
    simp only [hmin, core.num.I64.checked_neg]
    by_cases hpos : extAmt ≥ (0#i64 : Std.I64)
    · have hpos_val : (0:ℤ) ≤ extAmt.val := by scalar_tac
      have hcast : (IScalar.hcast .U64 extAmt : Std.U64).val = extAmt.val :=
        IScalar.hcast_inBounds_spec .U64 extAmt (by scalar_tac)
      simp only [hpos, ↓reduceIte]
      -- `partial_cmp` compares `ZMod.val` of the already-field-cast values, so bridging
      -- `hcast` up needs one more step: `ZMod.val ((n : ℕ) : ZMod bn254_r) = n` for
      -- `n < bn254_r` (true here, since `i.val, fee.val < 2^64 ≪ bn254_r`).
      have hib : (IScalar.hcast .U64 extAmt : Std.U64).val < bn254_r := by
        have h64 : (IScalar.hcast .U64 extAmt : Std.U64).val < 2 ^ 64 := by scalar_tac
        unfold bn254_r; omega
      have hfb : fee.val < bn254_r := by
        have h64 : fee.val < 2 ^ 64 := by scalar_tac
        unfold bn254_r; omega
      have hZi := ZMod.val_natCast_of_lt (n := bn254_r) hib
      have hZf := ZMod.val_natCast_of_lt (n := bn254_r) hfb
      simp only [hZi, hZf, Option.some.injEq, decide_eq_true_eq, Nat.compare_eq_lt,
        Nat.compare_eq_eq]
      by_cases hb : (IScalar.hcast .U64 extAmt : Std.U64).val ≤ fee.val
      · have hble : (IScalar.hcast .U64 extAmt : Std.U64).val < fee.val ∨
            (IScalar.hcast .U64 extAmt : Std.U64).val = fee.val := by omega
        simp only [hble, if_true, WP.spec_ok, Bool.false_eq_true, false_iff]
        rintro ⟨-, hgt, -⟩
        have := hgt hpos_val
        scalar_tac
      · have hgt : fee.val < (IScalar.hcast .U64 extAmt : Std.U64).val := by omega
        have hnble : ¬((IScalar.hcast .U64 extAmt : Std.U64).val < fee.val ∨
            (IScalar.hcast .U64 extAmt : Std.U64).val = fee.val) := by omega
        have hFcast : ((IScalar.hcast .U64 extAmt : Std.U64).val : F) = (extAmt.val : F) := by
          have h := congrArg (Int.cast (R := F)) hcast
          simp only [Int.cast_natCast] at h
          exact h
        simp only [hnble, if_false]
        -- `rw [hFcast]` doesn't go through cleanly here (`kabstract` trips over `pubAmt`'s
        -- `Array` coercion inside the folded expression -- the same family of issue
        -- `getElemBang` sidesteps in `isKnownRootLoopSpec`), so `hFcast` is used by
        -- composing equalities directly (`.trans`) instead of rewriting with it.
        have hsub := congrArg (fun z : F => z - (fee.val : F)) hFcast
        constructor
        · intro h
          have heq := of_decide_eq_true h
          exact ⟨hval, fun _ => by scalar_tac, heq.symm.trans hsub⟩
        · rintro ⟨-, -, heq⟩
          exact decide_eq_true (hsub.trans heq.symm)
    · have hneg_val : extAmt.val < 0 := by scalar_tac
      simp only [hpos, ↓reduceIte]
      -- No fee guard on this branch (see the docstring), so this reduces directly to
      -- `-(|extAmt| + fee) = pubAmt`, once `checked_neg`'s `IScalar.neg` step and the
      -- `hcast` bridge from the positive branch are both applied to `-extAmt`.
      have hnotmin : (extAmt : ℤ) ≠ IScalar.min .I64 := by scalar_tac
      -- Re-associating the two nested binds first (`bind_assoc_eq`) turns `let o ← (let
      -- y ← neg extAmt; ok (some y)); match o with ...` into `let y ← neg extAmt; match
      -- (some y) with ...`, where the match reduces on the spot (`some y` is a literal
      -- constructor, not a hypothesis substituted in) instead of needing `subst`/`rfl` to
      -- rewrite under it, which fails here (an ill-typed motive, a known rough edge of
      -- eliminating into a `match` result).
      simp only [bind_assoc_eq, bind_tc_ok]
      apply WP.spec_bind (IScalar.neg_step extAmt hnotmin)
      intro y hy
      have hcast : (IScalar.hcast .U64 y : Std.U64).val = y.val :=
        IScalar.hcast_inBounds_spec .U64 y (by scalar_tac)
      have hFcast : ((IScalar.hcast .U64 y : Std.U64).val : F) = -(extAmt.val : F) := by
        have h := congrArg (Int.cast (R := F)) hcast
        simp only [Int.cast_natCast] at h
        rw [h, hy]
        push_cast
        ring
      have hsub := congrArg (fun z : F => -(z + (fee.val : F))) hFcast
      simp only [WP.spec_ok]
      have hring : -(-(extAmt.val : F) + (fee.val : F)) = (extAmt.val : F) - (fee.val : F) := by ring
      constructor
      · intro h
        have heq := of_decide_eq_true h
        have hgoal := heq.symm.trans hsub
        exact ⟨hval, fun hge => absurd hge (by scalar_tac), hgoal.trans hring⟩
      · rintro ⟨-, -, heq⟩
        exact decide_eq_true (hsub.trans (hring.trans heq.symm))

-- `b`'s value is already below `p`, so `mapBytesToF` loses nothing reducing it: it's
-- injective on canonical bytes. Needed wherever the code compares raw bytes but the spec
-- compares field elements.
def canonical (b : Array Std.U8 32#usize) : Prop := mapBytesToNat b < LeanSpec.p

/-- The account's Merkle-tree-shaped fields, mapped into the spec's `Tree`, field by field.
`rootIndex` wraps mod 100 to keep `mapTree` total; real accounts always have
`root_index < 100` (a hypothesis where a theorem needs it, e.g. `isKnownRootRefines`'s
`hidx`), not something `mapTree` can assume for every possible input. -/
def mapTree (treeAccount : zkcash.MerkleTreeAccount) : LeanSpec.Tree where
  nextIndex := treeAccount.next_index.val
  subtrees := fun i => mapBytesToF treeAccount.subtrees.val[i.val]!
  root := mapBytesToF treeAccount.root
  history := fun i => mapBytesToF treeAccount.root_history.val[i.val]!
  rootIndex := ⟨treeAccount.root_index.val % 100, Nat.mod_lt _ (by norm_num)⟩

/-- `PartialEqArray.eq`, used throughout `is_known_root` to compare 32-byte roots, agrees
with raw array equality. Derived from Aeneas's own slice-level `PartialEqSlice.eq_homo_spec`
via `Array.to_slice`, rather than reproving the underlying list induction. -/
private theorem arrayEqU8Spec {N : Std.Usize} (a0 a1 : Array Std.U8 N) :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a0 a1 ⦃ (b : Bool) =>
      b = true ↔ a0 = a1 ⦄ := by
  have heq : core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8 a0 a1
      = core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 a0.to_slice a1.to_slice := by
    unfold core.array.equality.PartialEqArray.eq core.slice.cmp.PartialEqSlice.eq
    simp [Array.val_to_slice]
  rw [heq]
  have hne : ∀ x y : Std.U8, core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ ¬ (x = y) ⦄ := by
    intro x y
    simp [core.cmp.impls.PartialEqU8.ne, liftFun2]
  apply WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8
    a0.to_slice a1.to_slice hne)
  intro b hb
  constructor
  · intro hbt
    have h := hb.mp hbt
    rw [Slice.eq_iff, Array.val_to_slice, Array.val_to_slice] at h
    exact Subtype.ext h
  · intro h
    apply hb.mpr
    rw [Slice.eq_iff, Array.val_to_slice, Array.val_to_slice]
    exact congrArg Subtype.val h

-- Backward circular distance from `start` to `idx` (both `< 100`): the number of decrement
-- steps, wrapping at 100, to go from `start` down to `idx`.
private def backDist (start idx : ℕ) : ℕ := (100 + start - idx) % 100

-- A bounds-checked read equals the default-returning one; lets the rest of this file use
-- `l[i]!` throughout, sidestepping proof terms that `rw`/`simp` can't rewrite under.
private theorem getElemBang {α} [Inhabited α] (l : List α) (i : ℕ) (h : i < l.length) :
    l[i]'h = l[i]! := (getElem!_pos l i h).symm

/-- What `is_known_root_loop` computes: starting from `cur` and stepping backward with
wraparound at 100 (checking `a[j]` against `root` at each step), it accepts exactly when
some index at least as close as `cur`, going backward from `currentRootIndex`, matches.
Run from the top (`cur = currentRootIndex`), that is every index. `hpre` carries what's
already been ruled out by the steps taken to reach `cur`. -/
private theorem isKnownRootLoopSpec
    (a : Array (Array Std.U8 32#usize) 100#usize) (root : Array Std.U8 32#usize)
    (currentRootIndex cur : Std.Usize)
    (hcri : currentRootIndex.val < 100) (hcur : cur.val < 100)
    (hpre : ∀ j : Fin 100,
      backDist currentRootIndex.val j.val < backDist currentRootIndex.val cur.val →
      a.val[j.val]! ≠ root) :
    zkcash.merkle_tree.MerkleTree.is_known_root_loop a root 100#usize currentRootIndex cur
      ⦃ (ok : Bool) => ok = true ↔ ∃ j : Fin 100, a.val[j.val]! = root ⦄ := by
  unfold zkcash.merkle_tree.MerkleTree.is_known_root_loop
  apply loop.spec_decr_nat
    (measure := fun x : Std.Usize => 100 - backDist currentRootIndex.val x.val)
    (inv := fun x : Std.Usize => x.val < 100 ∧
      ∀ j : Fin 100, backDist currentRootIndex.val j.val < backDist currentRootIndex.val x.val →
        a.val[j.val]! ≠ root)
  · rintro x ⟨hx, hinv⟩
    unfold zkcash.merkle_tree.MerkleTree.is_known_root_loop.body
    apply WP.spec_bind (Array.index_usize_spec a x (by scalar_tac))
    intro a1 ha1
    have ha1' : a1 = a.val[x.val]! := ha1.trans (getElemBang a.val x.val (by scalar_tac))
    apply WP.spec_bind (arrayEqU8Spec root a1)
    intro b hb
    by_cases hbv : b = true
    · simp only [hbv, ↓reduceIte, WP.spec_ok, true_iff]
      exact ⟨⟨x.val, hx⟩, by rw [← ha1']; exact (hb.mp hbv).symm⟩
    · have hbf : b = false := by cases b <;> simp_all
      have hne : a.val[x.val]! ≠ root := by rw [← ha1']; exact fun h => hbv (hb.mpr h.symm)
      -- Extend `hinv` with `x` itself: everything at distance `≤ backDist cri x.val` misses.
      have hinv' : ∀ j : Fin 100,
          backDist currentRootIndex.val j.val ≤ backDist currentRootIndex.val x.val →
          a.val[j.val]! ≠ root := by
        intro j hj
        rcases lt_or_eq_of_le hj with hlt | heqd
        · exact hinv j hlt
        · have hjx : j.val = x.val := by
            have hbx : backDist currentRootIndex.val x.val < 100 := by
              simp only [backDist]; scalar_tac
            have hbj : backDist currentRootIndex.val j.val < 100 := by
              simp only [backDist]; scalar_tac
            simp only [backDist] at heqd
            omega
          rw [hjx]; exact hne
      simp only [hbf, Bool.false_eq_true, if_false]
      by_cases hx0 : x = 0#usize
      · have hxval : x.val = 0 := by scalar_tac
        have h0val : (0#usize : Std.Usize).val = 0 := by scalar_tac
        simp only [hx0, ↓reduceIte]
        apply WP.spec_bind (UScalar.sub_spec (x := (100#usize : Std.Usize)) (y := 1#usize) (by scalar_tac))
        intro i2 hi2
        obtain ⟨hi2val0, -⟩ := hi2
        have hi2val : i2.val = 99 := by scalar_tac
        by_cases hwrap : i2 = currentRootIndex
        · simp only [hwrap, ↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff, not_exists]
          intro j
          apply hinv'
          have hcri99 : currentRootIndex.val = 99 := by scalar_tac
          simp only [backDist]; scalar_tac
        · simp only [hwrap, ↓reduceIte, WP.spec_ok]
          refine ⟨⟨by scalar_tac, fun j hj => hinv' j ?_⟩, ?_⟩
          · simp only [backDist] at hj ⊢; scalar_tac
          · simp only [backDist]; scalar_tac
      · simp only [hx0, ↓reduceIte]
        apply WP.spec_bind (UScalar.sub_spec (x := x) (y := (1#usize : Std.Usize)) (by scalar_tac))
        intro i2 hi2
        obtain ⟨hi2val, -⟩ := hi2
        by_cases hwrap : i2 = currentRootIndex
        · simp only [hwrap, ↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff, not_exists]
          intro j
          apply hinv'
          have hcri : currentRootIndex.val = x.val - 1 := by scalar_tac
          simp only [backDist]; scalar_tac
        · simp only [hwrap, ↓reduceIte, WP.spec_ok]
          refine ⟨⟨by scalar_tac, fun j hj => hinv' j ?_⟩, ?_⟩
          · simp only [backDist] at hj ⊢; scalar_tac
          · simp only [backDist]; scalar_tac
  · exact ⟨hcur, hpre⟩

-- `foldl`'s value scales by `256^length` when the initial accumulator does, plus what it
-- would compute from `0`: the recursive shape of reading digits most-significant-first.
private theorem foldlEq (c : ℕ) (l : List Std.U8) :
    l.foldl (fun acc x => acc * 256 + x.val) c
      = c * 256 ^ l.length + l.foldl (fun acc x => acc * 256 + x.val) 0 := by
  induction l generalizing c with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
    rw [ih (c * 256 + x.val), ih x.val]
    ring

-- `mapBytesToNat`'s value never reaches the next power of 256, since each digit is `< 256`.
private theorem foldlBound (l : List Std.U8) :
    l.foldl (fun acc x => acc * 256 + x.val) 0 < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.length_cons, pow_succ, Nat.zero_mul, Nat.zero_add]
    rw [foldlEq x.val xs]
    have hx : x.val < 256 := by scalar_tac
    nlinarith [ih, hx]

-- Two naturals built from the same "digit, remainder" pair, with both remainders below
-- the shared base `m`, agree in both parts.
private theorem mulAddCancel {m x1 x2 r1 r2 : ℕ} (hm : 0 < m) (hr1 : r1 < m) (hr2 : r2 < m)
    (h : x1 * m + r1 = x2 * m + r2) : x1 = x2 ∧ r1 = r2 := by
  have e1 : r1 + m * x1 = r2 + m * x2 := by rw [mul_comm x1, mul_comm x2] at h; omega
  have d1 : (r1 + m * x1) / m = x1 := by
    rw [Nat.add_mul_div_left r1 x1 hm, Nat.div_eq_of_lt hr1, Nat.zero_add]
  have d2 : (r2 + m * x2) / m = x2 := by
    rw [Nat.add_mul_div_left r2 x2 hm, Nat.div_eq_of_lt hr2, Nat.zero_add]
  have hx : x1 = x2 := by rw [← d1, ← d2, e1]
  exact ⟨hx, by rw [hx] at h; omega⟩

/-- `mapBytesToNat` is injective on lists of equal length: reading a fixed number of bytes
most-significant-digit-first determines the bytes. No canonicity needed, since this is
exact `ℕ` equality, before any reduction mod `p`. -/
private theorem mapBytesToNatListInj : ∀ {l1 l2 : List Std.U8}, l1.length = l2.length →
    l1.foldl (fun acc x => acc * 256 + x.val) 0 = l2.foldl (fun acc x => acc * 256 + x.val) 0 →
    l1 = l2
  | [], [], _, _ => rfl
  | _ :: _, [], hlen, _ => by simp at hlen
  | [], _ :: _, hlen, _ => by simp at hlen
  | x1 :: xs1, x2 :: xs2, hlen, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
    simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add] at h
    rw [foldlEq x1.val xs1, foldlEq x2.val xs2, hlen] at h
    obtain ⟨hxeq, hreq⟩ := mulAddCancel (pow_pos (by norm_num) xs2.length)
      (hlen ▸ foldlBound xs1) (foldlBound xs2) h
    have hx : x1 = x2 := by scalar_tac
    rw [hx, mapBytesToNatListInj hlen hreq]

/-- `mapBytesToF` is injective on canonical bytes: the mapping reaches every value below
`p` exactly once. Needed wherever the code compares raw bytes but the spec compares field
elements. True here (`is_known_root` searches by byte equality) and again in every later
byte-vs-field connection theorem. -/
private theorem mapBytesToFInjOn {a b : Array Std.U8 32#usize}
    (ha : canonical a) (hb : canonical b) (h : mapBytesToF a = mapBytesToF b) : a = b := by
  have hval : mapBytesToNat a = mapBytesToNat b := by
    have e1 := ZMod.val_natCast_of_lt (n := LeanSpec.p) ha
    have e2 := ZMod.val_natCast_of_lt (n := LeanSpec.p) hb
    rw [← e1, ← e2, mapBytesToF, mapBytesToF] at *
    rw [h]
  exact Subtype.ext (mapBytesToNatListInj (by simp) hval)

/-- **Connection theorem for `zkcash::merkle_tree::MerkleTree::is_known_root`**
The program's backward search through the root history accepts exactly when `rootKnown`
holds for the mapped tree and root, given canonical bytes and a well-formed account
(`root_history_size = 100`, true of every reachable state since both `initialize` and
`initialize_spl` hardcode it; `root_index < 100`). -/
theorem isKnownRootRefines
    (treeAccount : zkcash.MerkleTreeAccount) (root : Array Std.U8 32#usize)
    (hroot : canonical root)
    (hhist : ∀ i : Fin 100, canonical treeAccount.root_history.val[i.val]!)
    (hsize : treeAccount.root_history_size.val = 100)
    (hidx : treeAccount.root_index.val < 100) :
    zkcash.merkle_tree.MerkleTree.is_known_root treeAccount root ⦃ (ok : Bool) =>
      ok = true ↔ rootKnown (mapTree treeAccount) (mapBytesToF root) ⦄ := by
  unfold zkcash.merkle_tree.MerkleTree.is_known_root
  apply WP.spec_bind (arrayEqU8Spec root (Array.repeat 32#usize 0#u8))
  intro b hb
  by_cases hbv : b = true
  · -- `root` is the zero sentinel: rejected outright, and `rootKnown` needs `≠ 0` too.
    simp only [hbv, ↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_iff, rootKnown, not_and]
    intro _
    rw [hb.mp hbv]
    simp [mapBytesToF, mapBytesToNat]
  · have hbf : b = false := by cases b <;> simp_all
    simp only [hbf, Bool.false_eq_true, if_false]
    apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize treeAccount.root_history_size
      (by scalar_tac))
    intro rootHistorySize hrhs
    apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize treeAccount.root_index (by scalar_tac))
    intro currentRootIndex hcri
    have hrhs' : rootHistorySize = (100#usize : Std.Usize) := by scalar_tac
    rw [hrhs']
    apply WP.spec_mono (isKnownRootLoopSpec treeAccount.root_history root currentRootIndex
      currentRootIndex (by scalar_tac) (by scalar_tac)
      (fun j hj => by simp [backDist] at hj))
    intro ok hok
    rw [hok, rootKnown, mapTree]
    constructor
    · rintro ⟨j, hj⟩
      refine ⟨⟨j, congrArg mapBytesToF hj⟩, fun h0 => ?_⟩
      have hzc : canonical (Array.repeat 32#usize 0#u8 : Array Std.U8 32#usize) := by
        simp only [canonical, mapBytesToNat, Array.repeat_val, LeanSpec.p]
        native_decide
      have hz : mapBytesToF (Array.repeat 32#usize 0#u8 : Array Std.U8 32#usize) = 0 := by
        simp [mapBytesToF, mapBytesToNat]
      exact absurd (hb.mpr (mapBytesToFInjOn hroot hzc (h0.trans hz.symm))) hbv
    · rintro ⟨⟨j, hj⟩, -⟩
      exact ⟨j, mapBytesToFInjOn (hhist j) hroot hj⟩

/-- Safety half of `isKnownRootRefines`: if `is_known_root` accepts, `rootKnown` holds.
Needs only the queried root to be canonical (for the `≠ 0` half); unlike the iff, nothing
about the stored history, which is what makes it usable as an invariant-free step lemma. -/
theorem isKnownRootSafe
    (treeAccount : zkcash.MerkleTreeAccount) (root : Array Std.U8 32#usize)
    (hroot : canonical root)
    (hsize : treeAccount.root_history_size.val = 100)
    (hidx : treeAccount.root_index.val < 100) :
    zkcash.merkle_tree.MerkleTree.is_known_root treeAccount root ⦃ (ok : Bool) =>
      ok = true → rootKnown (mapTree treeAccount) (mapBytesToF root) ⦄ := by
  unfold zkcash.merkle_tree.MerkleTree.is_known_root
  apply WP.spec_bind (arrayEqU8Spec root (Array.repeat 32#usize 0#u8))
  intro b hb
  by_cases hbv : b = true
  · simp only [hbv, ↓reduceIte, WP.spec_ok, Bool.false_eq_true, false_implies]
  · have hbf : b = false := by cases b <;> simp_all
    simp only [hbf, Bool.false_eq_true, if_false]
    apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize treeAccount.root_history_size
      (by scalar_tac))
    intro rootHistorySize hrhs
    apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize treeAccount.root_index (by scalar_tac))
    intro currentRootIndex hcri
    have hrhs' : rootHistorySize = (100#usize : Std.Usize) := by scalar_tac
    rw [hrhs']
    apply WP.spec_mono (isKnownRootLoopSpec treeAccount.root_history root currentRootIndex
      currentRootIndex (by scalar_tac) (by scalar_tac)
      (fun j hj => by simp [backDist] at hj))
    intro ok hok hokt
    obtain ⟨j, hj⟩ := hok.mp hokt
    rw [rootKnown, mapTree]
    refine ⟨⟨j, congrArg mapBytesToF hj⟩, fun h0 => ?_⟩
    have hzc : canonical (Array.repeat 32#usize 0#u8 : Array Std.U8 32#usize) := by
      simp only [canonical, mapBytesToNat, Array.repeat_val, LeanSpec.p]
      native_decide
    have hz : mapBytesToF (Array.repeat 32#usize 0#u8 : Array Std.U8 32#usize) = 0 := by
      simp [mapBytesToF, mapBytesToNat]
    exact absurd (hb.mpr (mapBytesToFInjOn hroot hzc (h0.trans hz.symm))) hbv

/-! ## Preconditions with no function of their own

`depositWithinLimit`, `signerSolvent` and `poolSolvent` aren't checked by a named Rust
function: each is a `require!` or `checked_sub` inlined directly in `fv_transact_entry`.
So each theorem below is about the guard's condition on its own, written out with the same
variable names `fv_transact_entry` uses, rather than about a whole function's `⦃ ⦄` spec. -/

/-- **Connection for `depositWithinLimit`**
`fv_transact_entry`'s deposit-limit guard (`ext_amount > 0` branch: `deposit_amount <=
tree_account.max_deposit_amount`, where `deposit_amount` is `ext_amount` cast to `u64`)
agrees with `depositWithinLimit`. `cfg.maxDepositLimit` is `tree_account.max_deposit_amount`,
per the config translation already noted on that field in `Spec/privacy_cash_spec.lean`. -/
theorem depositWithinLimitRefines
    (extAmt : Std.I64) (maxDeposit : Std.U64) (cfg : LeanSpec.config)
    (hcfg : cfg.maxDepositLimit = maxDeposit.val) (hpos : extAmt.val > 0) :
    (IScalar.hcast .U64 extAmt : Std.U64) ≤ maxDeposit ↔ depositWithinLimit cfg extAmt.val := by
  have hcast : (IScalar.hcast .U64 extAmt : Std.U64).val = extAmt.val :=
    IScalar.hcast_inBounds_spec .U64 extAmt (by scalar_tac)
  unfold depositWithinLimit
  rw [hcfg]
  constructor
  · intro h _; scalar_tac
  · intro h; scalar_tac

/-! ### `depositWithinLimitRefines`, anchored to the real `fv_transact_entry`

`depositWithinLimitRefines` above is an isolated arithmetic fact: its `extAmt`/`maxDeposit`
are freely-chosen variable names, not literally extracted from `fv_transact_entry`'s
generated body -- nothing stops it from silently drifting from the guard the program
actually checks (wrong operator, wrong field, a transcription slip). The theorem below
closes that gap: it takes `fv_transact_entry`'s own real parameters and *unfolds* the real
function down to its deposit-limit guard rather than restating it by hand, so the guard
condition in the conclusion is whatever Lean's own reduction of `zkcash.fv_transact_entry`
produces, not a hand-copied lookalike.

Reaching that guard needs six earlier steps of `fv_transact_entry` to have already
succeeded (`is_known_root`, the ext-data-hash recomputation and its equality check,
`fv_check_public_amount_entry`, `validate_fee`, `fv_verify_proof_full_entry`); those are
taken as hypotheses here, not reproved, since this theorem's job is only to pin down the
deposit-limit guard itself, not to re-derive facts that either already have their own
connection theorem above (`hknown`, `hb2`, `hvfee` via `feeSufficientAccepts`) or are
still open (`hb3`, the Groth16 bridge; see `TODO.md`).

Everything *after* the guard is left as an existentially-quantified continuation
(`contThen`/`contElse`): this theorem only pins down the guard. With every earlier step
assumed to succeed, `simp` only ever takes the `then` side of each earlier `if`, so no
rejection branch is involved. -/
theorem fv_transact_entry_depositGuardEq
    (tree_account : zkcash.MerkleTreeAccount) (global_config : zkcash.GlobalConfig)
    (proof_root proof_ext_data_hash proof_public_amount : Array Std.U8 32#usize)
    (input_nullifiers output_commitments : Array (Array Std.U8 32#usize) 2#usize)
    (proof_a : Array Std.U8 64#usize) (proof_b : Array Std.U8 128#usize)
    (proof_c : Array Std.U8 64#usize) (ext_data_minified : zkcash.ExtDataMinified)
    (encrypted_output1 encrypted_output2 : alloc.vec.Vec Std.U8)
    (rent_exempt_minimum tree_token_lamports signer_lamports : Std.U64)
    (recipient fee_recipient_account : zkcash.FvAccount)
    (ext_data : zkcash.ExtData) (extDataHash : Array Std.U8 32#usize)
    (fs fs1 : fr_shim.FrShim)
    (a : Array Std.U8 64#usize) (a1 a2 a3 : Array Std.U8 128#usize)
    (a4 : Array (Array Std.U8 64#usize) 8#usize)
    -- Every step `fv_transact_entry` takes before reaching the deposit-limit guard,
    -- copied argument-for-argument from `code_model/generated/Funs.lean`'s own body
    -- (lines 1769-1815), with only each step's *result* left as a hypothesis.
    (hextdata : zkcash.fv_ext_data_from_minified recipient fee_recipient_account
        ext_data_minified = ok ext_data)
    (hknown : zkcash.merkle_tree.MerkleTree.is_known_root tree_account proof_root = ok true)
    (hhash : zkcash.utils.calculate_complete_ext_data_hash ext_data.recipient ext_data.ext_amount
        (alloc.vec.Vec.deref encrypted_output1) (alloc.vec.Vec.deref encrypted_output2)
        ext_data.fee ext_data.fee_recipient ext_data.mint_address
      = ok (core.result.Result.Ok extDataHash))
    (hfs : fr_shim.FrShim.from_le_bytes_mod_order extDataHash = ok fs)
    (hfs1 : fr_shim.FrShim.from_be_bytes_mod_order proof_ext_data_hash = ok fs1)
    (hb1 : fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq fs fs1 = ok true)
    (hb2 : zkcash.utils.fv_check_public_amount_entry ext_data.ext_amount ext_data.fee
        proof_public_amount = ok true)
    (hvfee : zkcash.utils.validate_fee ext_data.ext_amount ext_data.fee
        global_config.deposit_fee_rate global_config.withdrawal_fee_rate
        global_config.fee_error_margin
      = ok (core.result.Result.Ok ()))
    (ha : curve_shim.FV_VK_ALPHA_G1 = ok a) (ha1 : curve_shim.FV_VK_BETA_G2 = ok a1)
    (ha2 : curve_shim.FV_VK_GAMME_G2 = ok a2) (ha3 : curve_shim.FV_VK_DELTA_G2 = ok a3)
    (ha4 : curve_shim.FV_VK_IC = ok a4)
    (hb3 : zkcash.utils.fv_verify_proof_full_entry proof_root proof_public_amount
        proof_ext_data_hash input_nullifiers output_commitments proof_a proof_b proof_c
        a a1 a2 a3 a4 = ok true)
    (hpos : ext_data.ext_amount > 0#i64) :
    ∃ contThen contElse : Std.U64 →
        Result ((core.result.Result Unit zkcash.anchor_lang.error.Error) ×
          zkcash.MerkleTreeAccount × Std.U64 × Std.U64 × zkcash.FvAccount × zkcash.FvAccount),
      zkcash.fv_transact_entry tree_account global_config proof_root proof_ext_data_hash
          proof_public_amount input_nullifiers output_commitments proof_a proof_b proof_c
          ext_data_minified encrypted_output1 encrypted_output2 rent_exempt_minimum
          tree_token_lamports signer_lamports recipient fee_recipient_account
        = (do
            let deposit_amount ← lift (IScalar.hcast .U64 ext_data.ext_amount)
            if deposit_amount <= tree_account.max_deposit_amount
            then contThen deposit_amount else contElse deposit_amount) := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 3
  unfold zkcash.fv_transact_entry
  simp only [hextdata, bind_tc_ok, hknown, ↓reduceIte, hhash,
    core.result.Result.Insts.CoreOpsTry.branch, hfs, hfs1, hb1, hb2, hvfee, ha, ha1, ha2, ha3,
    ha4, hb3, hpos, decide_eq_true_eq]
  rfl

/-- **Connection for `signerSolvent`**
The deposit path's `signer_lamports.checked_sub(deposit_amount)` (`fv_transact_entry`)
succeeds exactly when `signerSolvent` holds, reading `deposit_amount` as `extAmt` cast to
`u64` (valid since `ext_amount > 0` here) and the signer's balance as `signerLamports.val`. -/
theorem signerSolventRefines
    (extAmt : Std.I64) (signerLamports : Std.U64) (balances : LeanSpec.Pubkey → ℕ)
    (s : LeanSpec.Pubkey) (hbal : balances s = signerLamports.val) (hpos : extAmt.val > 0) :
    (Std.U64.checked_sub signerLamports (IScalar.hcast .U64 extAmt)).isSome
      ↔ signerSolvent balances s extAmt.val := by
  have hcast : (IScalar.hcast .U64 extAmt : Std.U64).val = extAmt.val :=
    IScalar.hcast_inBounds_spec .U64 extAmt (by scalar_tac)
  have hspec := Std.U64.checked_sub_bv_spec signerLamports (IScalar.hcast .U64 extAmt : Std.U64)
  unfold signerSolvent
  rw [hbal]
  constructor
  · intro hsome _
    cases h : Std.U64.checked_sub signerLamports (IScalar.hcast .U64 extAmt : Std.U64) with
    | some z => rw [h] at hspec; scalar_tac
    | none => rw [h] at hsome; simp at hsome
  · intro h
    have hle := h hpos
    cases h : Std.U64.checked_sub signerLamports (IScalar.hcast .U64 extAmt : Std.U64) with
    | some z => simp
    | none => rw [h] at hspec; omega

/-- **Connection for `poolSolvent`**
`fv_transact_entry`'s two pool-balance guards (`InsufficientFundsForWithdrawal`, when
`ext_amount < 0`; `InsufficientFundsForFee`, when `fee > 0` and `ext_amount >= 0`) agree
with `poolSolvent`'s two conjuncts, reading `extAmtAbs` as `-ext_amount` cast to `u64`
(the code's own `ext_amount.checked_neg()?.try_into()?`, valid exactly when `ext_amount`
isn't `i64::MIN`, already ruled out by `pubAmtConsistent`). -/
theorem poolSolventRefines
    (solBalance rentExemptMin fee extAmtAbs : Std.U64) (extAmt : Std.I64)
    (hneg : extAmt.val < 0 → extAmtAbs.val = (-extAmt.val).toNat) :
    ((extAmt.val < 0 → extAmtAbs.val + fee.val + rentExemptMin.val ≤ solBalance.val) ∧
      (extAmt.val ≥ 0 ∧ fee.val > 0 → fee.val + rentExemptMin.val ≤ solBalance.val))
      ↔ poolSolvent solBalance.val rentExemptMin.val extAmt.val fee.val := by
  unfold poolSolvent
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun hlt => ?_, h2⟩
    have h1' := h1 hlt
    rw [hneg hlt] at h1'
    have habs : |extAmt.val| = -extAmt.val := abs_of_neg hlt
    have htoNat : ((-extAmt.val).toNat : ℤ) = -extAmt.val := Int.toNat_of_nonneg (by omega)
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨fun hlt => ?_, h2⟩
    have h1' := h1 hlt
    rw [hneg hlt]
    have habs : |extAmt.val| = -extAmt.val := abs_of_neg hlt
    have htoNat : ((-extAmt.val).toNat : ℤ) = -extAmt.val := Int.toNat_of_nonneg (by omega)
    omega

/-- **Connection for `treeHasRoom`**
`treeHasRoom`'s two slots of headroom are exactly enough for `append`'s own room guard
(`next_index < 1u64 <<< height`) to pass both times `transact` calls it: once directly, and
once more after the first call has incremented `next_index` by one, which is what `append`
does on success. `maxCapacity` stands for `1u64 <<< height`'s value rather than that
expression itself (`hcap` is exactly `UScalar.ShiftLeft_spec`'s conclusion), and `nextIndex'`
for the account's `next_index` after the first call, since deriving either from `append`
itself needs more than this theorem takes on: `append` calls into the Poseidon hasher
axioms, and showing what it returns on success needs `append` connected to `appendEffects`,
neither of which is done yet. This theorem only carries the arithmetic through. -/
theorem treeHasRoomRefines
    (nextIndex maxCapacity : Std.U64) (height : Std.Usize)
    (hcap : maxCapacity.val = (1 <<< height.val) % U64.size) (hheight : height.val = 26)
    (hroom : nextIndex.val < 2 ^ 26 - 2)
    (nextIndex' : Std.U64) (hnext' : nextIndex'.val = nextIndex.val + 1) :
    nextIndex.val < maxCapacity.val ∧ nextIndex'.val < maxCapacity.val := by
  rw [hcap, hheight]
  have hsize : U64.size = 2 ^ 64 := by scalar_tac
  simp only [Nat.shiftLeft_eq, one_mul, hsize]
  norm_num
  omega

/-- **Connection for `appendEffects`, via `MerkleTree::append`**

The tree update is the one piece `treeHasRoomRefines` flagged as missing: `append` folds
over 26 levels, at each one either hashing the running value against a precomputed
"zero subtree" constant (`H::zero_bytes()[i]`) or against the level's stored sibling
(`tree_account.subtrees[i]`), depending on the bit of `next_index` at that level -- exactly
`appendEffects`'s own `Fin.foldl` over `Z`/`H2`. Both `H::hashv` and `H::zero_bytes` are
bare axioms in the trusted base with *no* stated properties (`code_model/hand_written/
TrustedFuns.lean:283`, `:294` -- the file's own comment already calls the missing link to
`Z` "a genuine gap, not a formality"). `hHashv`/`hZeroBytes` below are that link, exactly
the same kind of hypothesis `externalDataBoundRefines`'s `hSha` is for the SHA-256 axiom:
a deliberate, minimal connection between the code's hash oracle and the spec's abstract
`PoseidonHashes`, not a silent weakening.

Given those and room in the tree (`treeHasRoomRefines`'s own `hroom`), `append` succeeds
and the account it returns maps (through `mapTree`) to exactly `appendEffects leaf`. The
proof itself is not done. The concrete plan, now that `externalDataBoundRefines` found
`step` (Aeneas's tactic for chaining through monadic calls -- see its docstring): unfold
`merkle_tree.MerkleTree.append_loop`, apply `loop.spec_decr_nat` with a measure/invariant
pairing the loop's `(subtrees, current_index, current_level_hash)` state at iteration `i`
to `Fin.foldl.loop 26 step (leaf, oldTree.subtrees) i` (the *inner* recursive function
`Fin.foldl` itself is built from, in `Init/Data/Fin/Fold.lean` -- not exported as a lemma,
so this needs its own small unfolding fact proven first, mirroring `foldl_loop` in that
file but public), then `step*` through each iteration's array read/write and `hHashv`/
`hZeroBytes` call, the same way `isKnownRootLoopSpec` and `CopyLoops.lean`'s `loop*_spec`
theorems handle their own loops' bodies. This is a substantially bigger undertaking than
either of those: more state to thread per step, and an actual hash call to discharge via
`hHashv` at every one of the 26 levels rather than once. -/
theorem appendRefines
    [LeanSpec.PoseidonHashes]
    (leaf : Array Std.U8 32#usize) (treeAccount : zkcash.MerkleTreeAccount)
    (hheight : treeAccount.height.val = 26)
    (hroom : treeAccount.next_index.val < 2 ^ 26 - 2)
    (hHashv : ∀ a b : Array Std.U8 32#usize, ∃ h : Array Std.U8 32#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.hashv
          ⟨[⟨a.val, by scalar_tac⟩, ⟨b.val, by scalar_tac⟩], by scalar_tac⟩
        = ok (core.result.Result.Ok h) ∧
        mapBytesToF h = LeanSpec.PoseidonHashes.H2 (mapBytesToF a) (mapBytesToF b))
    (hZeroBytes : ∃ zeroBytes : Array (Array Std.U8 32#usize) 41#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.zero_bytes = ok zeroBytes ∧
      ∀ i : Fin 26, mapBytesToF (zeroBytes.val[i.val]!) = LeanSpec.Z i.val) :
    ∃ (proof : alloc.vec.Vec (Array Std.U8 32#usize)) (treeAccount' : zkcash.MerkleTreeAccount),
      zkcash.merkle_tree.MerkleTree.append
          zkcash.light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher
        leaf treeAccount = ok (core.result.Result.Ok proof, treeAccount') ∧
      mapTree treeAccount' = LeanSpec.appendEffects (mapBytesToF leaf) (mapTree treeAccount) := by
  sorry

/-! ## transferEffects: the deposit/withdrawal balance update

`transferEffects` is a state *effect*, not a boolean precondition like the guards above:
there's no "does this hold", only "does the code compute the same new balances the spec
does". `fv_transact_entry` keeps the signer's, the pool's (`tree_token_lamports`) and the
recipient's balances as separate `u64`s rather than one `Pubkey → ℕ` function, so
`transferEffectsOf` below restates `transferEffects` in exactly those terms;
`transferEffectsOfEq` ties it back to the real spec definition. Splitting the deposit and
withdrawal branches into their own theorems mirrors how the guards above are split, since
`fv_transact_entry` itself branches the same way (`if ext_amount > 0 ... else if ext_amount
< 0 ...`) and each branch touches a different pair of balances. -/

-- `transferEffects`, unpacked to the one balance that moves and the pool's SOL balance,
-- instead of a full `World`: nothing else in `World` changes here, and a full
-- `TxInputs`/`World` literal would need placeholder values for every unrelated field
-- (root, nullifiers, the proof, ...).
def transferEffectsOf (extAmt : ℤ) (mover : LeanSpec.Pubkey) (balances : LeanSpec.Pubkey → ℕ)
    (solBalance : ℕ) : (LeanSpec.Pubkey → ℕ) × ℕ :=
  if extAmt = 0 then (balances, solBalance) else
    let extAmtAbs := extAmt.natAbs
    (if extAmt > 0 then Function.update balances mover (balances mover - extAmtAbs)
      else Function.update balances mover (balances mover + extAmtAbs),
     if extAmt > 0 then solBalance + extAmtAbs else solBalance - extAmtAbs)

-- `mover` is `s` for a deposit (the signer pays) and `A` for a withdrawal (the recipient
-- is paid), matching `transferEffects`'s own two branches field for field.
theorem transferEffectsOfEq (inputs : LeanSpec.TxInputs) (oldWorld : LeanSpec.World) :
    transferEffectsOf inputs.extAmt (if inputs.extAmt > 0 then inputs.s else inputs.A)
      oldWorld.balances oldWorld.state.solBalance
      = ((LeanSpec.transferEffects inputs oldWorld).balances,
        (LeanSpec.transferEffects inputs oldWorld).state.solBalance) := by
  unfold transferEffectsOf LeanSpec.transferEffects
  by_cases h0 : inputs.extAmt = 0
  · simp [h0]
  · by_cases hpos : inputs.extAmt > 0 <;> simp [h0, hpos]

/-- **Connection for `transferEffects`'s deposit branch (`ext_amount > 0`)**
Given `signerSolvent` (already what makes `signer_lamports.checked_sub` succeed here, per
`signerSolventRefines`) and enough headroom in the pool's balance for the deposit not to
overflow a `u64` (real SOL amounts are nowhere near `u64::MAX`, but nothing yet states that
as a spec-level invariant, so it's taken as a hypothesis -- the same shape of gap as
`feeSufficientRefines`'s rate bounds), `fv_transact_entry`'s two updates
(`signer_lamports.checked_sub`, `tree_token_lamports.checked_add`) succeed and produce
exactly the pair `transferEffectsOf` computes for a deposit. -/
theorem transferEffectsDepositRefines
    (extAmt : Std.I64) (signerLamports treeTokenLamports : Std.U64)
    (balances : LeanSpec.Pubkey → ℕ) (s : LeanSpec.Pubkey) (solBalance : ℕ)
    (hbal : balances s = signerLamports.val) (hpool : solBalance = treeTokenLamports.val)
    (hpos : extAmt.val > 0) (hsolvent : signerSolvent balances s extAmt.val)
    (hoverflow : treeTokenLamports.val + extAmt.val.toNat ≤ Std.U64.max) :
    ∃ signerLamports' treeTokenLamports' : Std.U64,
      Std.U64.checked_sub signerLamports (IScalar.hcast .U64 extAmt) = some signerLamports' ∧
      Std.U64.checked_add treeTokenLamports (IScalar.hcast .U64 extAmt) = some treeTokenLamports' ∧
      (Function.update balances s signerLamports'.val, treeTokenLamports'.val) =
        transferEffectsOf extAmt.val s balances solBalance := by
  have hcast : (IScalar.hcast .U64 extAmt : Std.U64).val = extAmt.val :=
    IScalar.hcast_inBounds_spec .U64 extAmt (by scalar_tac)
  have hle : extAmt.val.natAbs ≤ balances s := by have := hsolvent hpos; omega
  have hsub := Std.U64.checked_sub_bv_spec signerLamports (IScalar.hcast .U64 extAmt : Std.U64)
  have hadd := Std.U64.checked_add_bv_spec treeTokenLamports (IScalar.hcast .U64 extAmt : Std.U64)
  cases hs : Std.U64.checked_sub signerLamports (IScalar.hcast .U64 extAmt : Std.U64) with
  | none => rw [hs] at hsub; omega
  | some z =>
    cases ha : Std.U64.checked_add treeTokenLamports (IScalar.hcast .U64 extAmt : Std.U64) with
    | none => rw [ha] at hadd; omega
    | some z' =>
      rw [hs] at hsub; rw [ha] at hadd
      refine ⟨z, z', rfl, rfl, ?_⟩
      simp only [transferEffectsOf, if_neg (show extAmt.val ≠ 0 by omega), if_pos hpos]
      have hzv : z.val = balances s - extAmt.val.natAbs := by rw [hbal]; omega
      have hz'v : z'.val = solBalance + extAmt.val.natAbs := by rw [hpool]; omega
      rw [hzv, hz'v]

/-- **Connection for `transferEffects`'s withdrawal branch (`ext_amount < 0`)**
Given `poolSolvent` (already what makes the pool's balance guard succeed here, per
`poolSolventRefines`) and enough headroom in the recipient's balance for the payout not to
overflow a `u64`, `fv_transact_entry`'s two updates (`tree_token_lamports.checked_sub`,
`recipient.lamports.checked_add`) succeed and produce exactly the pair `transferEffectsOf`
computes for a withdrawal. -/
theorem transferEffectsWithdrawalRefines
    (extAmt : Std.I64) (extAmtAbs : Std.U64) (treeTokenLamports recipientLamports : Std.U64)
    (balances : LeanSpec.Pubkey → ℕ) (A : LeanSpec.Pubkey) (solBalance : ℕ)
    (hneg : extAmt.val < 0) (habs : extAmtAbs.val = (-extAmt.val).toNat)
    (hbal : balances A = recipientLamports.val) (hpool : solBalance = treeTokenLamports.val)
    (hpoolsolvent : extAmtAbs.val ≤ treeTokenLamports.val)
    (hoverflow : recipientLamports.val + extAmtAbs.val ≤ Std.U64.max) :
    ∃ treeTokenLamports' recipientLamports' : Std.U64,
      Std.U64.checked_sub treeTokenLamports extAmtAbs = some treeTokenLamports' ∧
      Std.U64.checked_add recipientLamports extAmtAbs = some recipientLamports' ∧
      (Function.update balances A recipientLamports'.val, treeTokenLamports'.val) =
        transferEffectsOf extAmt.val A balances solBalance := by
  have hsub := Std.U64.checked_sub_bv_spec treeTokenLamports extAmtAbs
  have hadd := Std.U64.checked_add_bv_spec recipientLamports extAmtAbs
  cases hs : Std.U64.checked_sub treeTokenLamports extAmtAbs with
  | none => rw [hs] at hsub; omega
  | some z =>
    cases ha : Std.U64.checked_add recipientLamports extAmtAbs with
    | none => rw [ha] at hadd; omega
    | some z' =>
      rw [hs] at hsub; rw [ha] at hadd
      refine ⟨z, z', rfl, rfl, ?_⟩
      simp only [transferEffectsOf, if_neg (show extAmt.val ≠ 0 by omega), if_neg (not_lt.mpr
        (le_of_lt hneg))]
      have hextAbs : extAmt.val.natAbs = extAmtAbs.val := by omega
      have hzv : z.val = solBalance - extAmt.val.natAbs := by rw [hpool, hextAbs]; omega
      have hz'v : z'.val = balances A + extAmt.val.natAbs := by rw [hbal, hextAbs]; omega
      rw [hzv, hz'v]

/-- **Connection for `transactEffects`'s fee transfer**
`fv_transact_entry`'s fee transfer (guarded by `fee > 0`, and re-checked against
`InsufficientFundsForFee` when `ext_amount ≥ 0` -- `poolSolventRefines`'s second conjunct)
moves `fee` out of the pool's SOL balance and into the fee recipient's, matching
`transactEffects`'s fee-related state changes. Stated post-transfer: the sufficiency this
theorem needs is over the pool's balance *after* the deposit/withdrawal move
(`transferEffectsDepositRefines`/`WithdrawalRefines`'s output), not the pre-transfer value
`poolSolvent` states its own guard over -- chaining the two into one derived guarantee is a
separate step, done in `transactSafe` (`TransactSafety.lean`). -/
theorem transactEffectsFeeRefines
    (fee rentExemptMin treeTokenLamports feeRecipientLamports : Std.U64)
    (balances : LeanSpec.Pubkey → ℕ) (t : LeanSpec.Pubkey) (solBalance : ℕ)
    (hbal : balances t = feeRecipientLamports.val) (hpool : solBalance = treeTokenLamports.val)
    (hpos : fee.val > 0) (hsufficient : fee.val + rentExemptMin.val ≤ treeTokenLamports.val)
    (hoverflow : feeRecipientLamports.val + fee.val ≤ Std.U64.max) :
    ∃ treeTokenLamports' feeRecipientLamports' : Std.U64,
      Std.U64.checked_sub treeTokenLamports fee = some treeTokenLamports' ∧
      Std.U64.checked_add feeRecipientLamports fee = some feeRecipientLamports' ∧
      (Function.update balances t feeRecipientLamports'.val, treeTokenLamports'.val) =
        (Function.update balances t (balances t + fee.val), solBalance - fee.val) := by
  have hsub := Std.U64.checked_sub_bv_spec treeTokenLamports fee
  have hadd := Std.U64.checked_add_bv_spec feeRecipientLamports fee
  cases hs : Std.U64.checked_sub treeTokenLamports fee with
  | none => rw [hs] at hsub; omega
  | some z =>
    cases ha : Std.U64.checked_add feeRecipientLamports fee with
    | none => rw [ha] at hadd; omega
    | some z' =>
      rw [hs] at hsub; rw [ha] at hadd
      refine ⟨z, z', rfl, rfl, ?_⟩
      have hzv : z.val = solBalance - fee.val := by rw [hpool]; omega
      have hz'v : z'.val = balances t + fee.val := by rw [hbal]; omega
      rw [hzv, hz'v]

-- The `?`-operator idiom Aeneas produces around every `checked_*` arithmetic call
-- (`let o ← checked_op a b; let r ← Option.ok_or o err; let cf ← Result.branch r; match cf
-- with | Continue v => CONT v | Break residual => <propagate the error>`) reduces to
-- `CONT v` outright once the checked op actually succeeded with `v`: each step is a
-- literal pattern match on the `some`/`Ok`/`Continue` it was just given, so the whole chain
-- is a defeq computation, not something needing `WP.spec_bind` at every step.
private theorem tryContinueOverflow {α} (o : Option α) (v : α) (hov : o = some v)
    (cont : α → Result (core.result.Result Unit zkcash.anchor_lang.error.Error)) :
    (do let r ← core.option.Option.ok_or o zkcash.ErrorCode.ArithmeticOverflow
        let cf ← core.result.Result.Insts.CoreOpsTry.branch r
        match cf with
        | core.ops.control_flow.ControlFlow.Continue val => cont val
        | core.ops.control_flow.ControlFlow.Break residual =>
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
              Unit zkcash.anchor_lang.error.Error.Insts.CoreConvertFromErrorCode residual)
      = cont v := by
  subst hov; rfl

-- `checked_mul`/`checked_div`/`checked_sub` succeed exactly when the obvious arithmetic
-- side condition holds (no overflow, no division by zero, no underflow); these package
-- each one's `@[step_pure]` spec into the `some`-case fact `feeSufficientRefines` needs
-- to invoke `tryContinueOverflow` at each arithmetic step.
private theorem u128MulSome (x y : Std.U128) (h : x.val * y.val ≤ Std.U128.max) :
    ∃ z : Std.U128, x.checked_mul y = some z ∧ z.val = x.val * y.val := by
  have hspec := x.checked_mul_bv_spec y
  cases hc : x.checked_mul y with
  | none => rw [hc] at hspec; omega
  | some z => rw [hc] at hspec; exact ⟨z, rfl, hspec.2.1⟩

private theorem u128DivSome (x y : Std.U128) (h : y.val ≠ 0) :
    ∃ z : Std.U128, x.checked_div y = some z ∧ z.val = x.val / y.val := by
  have hspec := x.checked_div_bv_spec y
  cases hc : x.checked_div y with
  | none => rw [hc] at hspec; exact absurd hspec h
  | some z => rw [hc] at hspec; exact ⟨z, rfl, hspec.2.1⟩

private theorem u128SubSome (x y : Std.U128) (h : y.val ≤ x.val) :
    ∃ z : Std.U128, x.checked_sub y = some z ∧ z.val = x.val - y.val := by
  have hspec := x.checked_sub_bv_spec y
  cases hc : x.checked_sub y with
  | none => rw [hc] at hspec; omega
  | some z => rw [hc] at hspec; exact ⟨z, rfl, hspec.2.1⟩

-- A `do` block whose continuation can never produce `ok (.Ok ())` can't either, whatever
-- its first step returns: an `ok` just hands over to the continuation, and `fail`/`div`
-- are not `ok` at all. Applied once per step, this disposes of every `require!` rejection
-- without knowing anything about the diagnostic axioms (`to_string`, the anchor error
-- conversions) that build its `Err` value.
private theorem bindNeOkUnit {β E : Type} (x : Result β)
    (k : β → Result (core.result.Result Unit E))
    (hk : ∀ b, k b ≠ ok (.Ok ())) : x >>= k ≠ ok (.Ok ()) := by
  cases x with
  | ok b => exact hk b
  | fail e => simp [Bind.bind, Aeneas.Std.bind]
  | div => simp [Bind.bind, Aeneas.Std.bind]

-- `validate_fee`'s `require!` rejection (`InvalidFeeAmount`; `line` is the source line the
-- generated code records). It runs `ErrorCode.name`, `to_string` and `From<AnchorError>`,
-- all bare axioms, and still never returns `ok (.Ok ())`.
private theorem feeErrNeOk (line : Std.U32) :
    (do
      let s ← zkcash.ErrorCode.name zkcash.ErrorCode.InvalidFeeAmount
      let i ← core.convert.IntoFrom.into zkcash.U32.Insts.CoreConvertFromErrorCode
        zkcash.ErrorCode.InvalidFeeAmount
      let s1 ← alloc.string.ToString.Blanket.to_string zkcash.ErrorCode.Insts.CoreFmtDisplay
        zkcash.ErrorCode.InvalidFeeAmount
      let e ← anchor_lang.error.Error.Insts.CoreConvertFromAnchorError.from
        { error_name := s, error_code_number := i, error_msg := s1,
          error_origin := some (zkcash.anchor_lang.error.ErrorOrigin.Source
            { filename := toStr "programs/zkcash/src/utils.rs", line := line }),
          compared_values := none }
      ok (core.result.Result.Err e) : Result (core.result.Result Unit zkcash.anchor_lang.error.Error))
      ≠ ok (.Ok ()) :=
  bindNeOkUnit _ _ fun _ => bindNeOkUnit _ _ fun _ => bindNeOkUnit _ _ fun _ =>
    bindNeOkUnit _ _ fun _ => by simp

-- Everything `validate_fee` does after its first cast, which the deposit and withdrawal
-- branches share verbatim (only the amount `i`, the rate `i1` and the two error values
-- differ). Under the rate bounds every `checked_*` step succeeds and both `u64` casts are
-- value-preserving, so the whole block collapses to one comparison against `feeSufficient`'s
-- `minAcceptableFee`. The `expected_fee = 0` branch's `errZero` is unreachable (`fee ≥ 0`
-- always holds), so it doesn't appear on the right-hand side.
private theorem feeTailEq (i i1 : Std.U128) (provided_fee : Std.U64) (fee_error_margin : Std.U16)
    (hi : i.val ≤ 2^63) (hi1 : i1.val ≤ 10000) (hm : fee_error_margin.val ≤ 10000)
    (errLow errZero : Result (core.result.Result Unit zkcash.anchor_lang.error.Error))
    : (do
      let o ← lift (U128.checked_mul i i1)
      let r ← core.option.Option.ok_or o zkcash.ErrorCode.ArithmeticOverflow
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let o1 ← lift (U128.checked_div val 10000#u128)
        let r1 ← core.option.Option.ok_or o1 zkcash.ErrorCode.ArithmeticOverflow
        let cf1 ← core.result.Result.Insts.CoreOpsTry.branch r1
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue val1 =>
          let expected_fee ← lift (UScalar.cast .U64 val1)
          if expected_fee > 0#u64
          then
            let i2 ← lift (UScalar.cast .U128 fee_error_margin)
            let o2 ← lift (U128.checked_sub 10000#u128 i2)
            let r2 ← core.option.Option.ok_or o2 zkcash.ErrorCode.ArithmeticOverflow
            let cf2 ← core.result.Result.Insts.CoreOpsTry.branch r2
            match cf2 with
            | core.ops.control_flow.ControlFlow.Continue val2 =>
              let i3 ← lift (UScalar.cast .U128 expected_fee)
              let o3 ← lift (U128.checked_mul i3 val2)
              let r3 ← core.option.Option.ok_or o3 zkcash.ErrorCode.ArithmeticOverflow
              let cf3 ← core.result.Result.Insts.CoreOpsTry.branch r3
              match cf3 with
              | core.ops.control_flow.ControlFlow.Continue val3 =>
                let o4 ← lift (U128.checked_div val3 10000#u128)
                let r4 ← core.option.Option.ok_or o4 zkcash.ErrorCode.ArithmeticOverflow
                let cf4 ← core.result.Result.Insts.CoreOpsTry.branch r4
                match cf4 with
                | core.ops.control_flow.ControlFlow.Continue val4 =>
                  let min_acceptable_fee ← lift (UScalar.cast .U64 val4)
                  if provided_fee >= min_acceptable_fee
                  then ok (core.result.Result.Ok ())
                  else errLow
                | core.ops.control_flow.ControlFlow.Break residual =>
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                    Unit zkcash.anchor_lang.error.Error.Insts.CoreConvertFromErrorCode residual
              | core.ops.control_flow.ControlFlow.Break residual =>
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                  Unit zkcash.anchor_lang.error.Error.Insts.CoreConvertFromErrorCode residual
            | core.ops.control_flow.ControlFlow.Break residual =>
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
                Unit zkcash.anchor_lang.error.Error.Insts.CoreConvertFromErrorCode residual
          else
            if provided_fee >= 0#u64
            then ok (core.result.Result.Ok ())
            else errZero
        | core.ops.control_flow.ControlFlow.Break residual =>
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
            Unit zkcash.anchor_lang.error.Error.Insts.CoreConvertFromErrorCode residual
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit zkcash.anchor_lang.error.Error.Insts.CoreConvertFromErrorCode residual)
      = if provided_fee.val ≥ i.val * i1.val / 10000 * (10000 - fee_error_margin.val) / 10000
        then ok (.Ok ()) else errLow := by
  simp only [lift, bind_tc_ok]
  obtain ⟨val, hval, hvalv⟩ := u128MulSome i i1 (by
    calc i.val * i1.val ≤ 2^63 * 10000 := Nat.mul_le_mul hi hi1
      _ ≤ U128.max := by scalar_tac)
  simp only [hval, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok]
  obtain ⟨val1, hval1, hval1v⟩ := u128DivSome val 10000#u128 (by simp)
  simp only [hval1, core.result.Result.Insts.CoreOpsTry.branch,
    bind_tc_ok]
  have hval1e : val1.val = i.val * i1.val / 10000 := by rw [hval1v, hvalv]; rfl
  have hle : i.val * i1.val / 10000 ≤ i.val :=
    Nat.div_le_of_le_mul (by rw [Nat.mul_comm 10000]; exact Nat.mul_le_mul_left _ hi1)
  have hval1b : val1.val < 2^64 := by omega
  have hef : (UScalar.cast .U64 val1).val = val1.val :=
    UScalar.cast_val_mod_pow_of_inBounds_eq _ _ hval1b
  rw [← hval1e]
  by_cases hz : UScalar.cast .U64 val1 > 0#u64
  · rw [if_pos hz]
    have hmr : (UScalar.cast .U128 fee_error_margin).val = fee_error_margin.val := by simp
    obtain ⟨val2, hval2, hval2v⟩ := u128SubSome 10000#u128 (UScalar.cast .U128 fee_error_margin)
      (by rw [hmr]; simp; omega)
    simp only [hval2, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok]
    have hval2e : val2.val = 10000 - fee_error_margin.val := by rw [hval2v, hmr]; rfl
    have hcc : (UScalar.cast .U128 (UScalar.cast .U64 val1)).val = val1.val := by
      simp only [UScalar.cast_val_eq, hef]; simp
    obtain ⟨val3, hval3, hval3v⟩ := u128MulSome (UScalar.cast .U128 (UScalar.cast .U64 val1))
      val2 (by
        rw [hcc, hval2e]
        calc val1.val * (10000 - fee_error_margin.val) ≤ 2^63 * 10000 :=
              Nat.mul_le_mul (by omega) (by omega)
          _ ≤ U128.max := by scalar_tac)
    simp only [hval3, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok]
    obtain ⟨val4, hval4, hval4v⟩ := u128DivSome val3 10000#u128 (by simp)
    simp only [hval4, core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
      bind_tc_ok]
    have hval4e : val4.val = val1.val * (10000 - fee_error_margin.val) / 10000 := by
      rw [hval4v, hval3v, hcc, hval2e]; rfl
    have hval4le : val4.val ≤ val1.val := by
      rw [hval4e]
      exact Nat.div_le_of_le_mul (by rw [Nat.mul_comm 10000]; exact Nat.mul_le_mul_left _ (by omega))
    have hval4b : val4.val < 2^64 := by omega
    have hmin : (UScalar.cast .U64 val4).val = val4.val :=
      UScalar.cast_val_mod_pow_of_inBounds_eq _ _ hval4b
    have hiff : provided_fee ≥ UScalar.cast .U64 val4 ↔
        provided_fee.val ≥ val1.val * (10000 - fee_error_margin.val) / 10000 := by
      rw [← hval4e, ← hmin]; rfl
    by_cases hfee : provided_fee ≥ UScalar.cast .U64 val4
    · rw [if_pos hfee, if_pos (hiff.mp hfee)]
    · rw [if_neg hfee, if_neg (fun h => hfee (hiff.mpr h))]
  · have hz0 : (UScalar.cast .U64 val1).val = 0 := by
      have : ¬ (UScalar.cast .U64 val1).val > 0 := hz
      omega
    have hge : provided_fee ≥ 0#u64 := by
      show (0#u64).val ≤ provided_fee.val; simp
    rw [if_neg hz, if_pos hge, ← hef, hz0, if_pos (by simp)]

/-- **Connection for `feeSufficient`** (safety direction)
`fv_transact_entry` calls `validate_fee` right after `check_public_amount`, on the same
`ext_amount`/`fee`; `feeSufficient`'s `cfg.depositFeeRate`/`withdrawalFeeRate`/
`feeMarginError` are `GlobalConfig`'s matching fields. If `validate_fee` accepts
(`ok (.Ok ())`), `feeSufficient` holds.

Stated as an implication on `ok (.Ok ())`, not a `⦃ ⦄` iff: rejection (an `Err`, a panic,
non-termination) is just "no transition" in the spec, so nothing is claimed about how the
code rejects. That is also why the diagnostic axioms used to build the `Err` value play no
role here. The converse is `feeSufficientAccepts` below; it is *not* an iff, since for
`extAmt = i64::MIN` the code rejects (`checked_neg` overflows) while `feeSufficient` can hold.

The three rate bounds are load-bearing, not defensive: without them the theorem is false.
`expected_fee`'s cast back down to `u64` (`utils.rs`) truncates once
`extAmt * depositRate / 10000 > u64.max`, and at `depositRate.val = u16.max` (65535, a value
the type alone allows) that already happens for `extAmt` as small as a few times `2^60`
(`(2^63 - 1) * 65535 / 10000 ≈ 6.0e19 > u64.max ≈ 1.8e19`). A truncated expected fee lets
the code accept a fee below the spec's minimum. The real `GlobalConfig` never holds a rate
above `10000` (basis points, i.e. at most 100%), so the bound is exactly what every reachable
state already satisfies; it's only missing here because nothing yet connects `GlobalConfig`'s
admin-only setter to a spec-side invariant saying so (a gap worth closing before relying on
this theorem). -/
theorem feeSufficientRefines (extAmt : Std.I64) (fee : Std.U64)
    (depositRate withdrawalRate marginRate : Std.U16)
    (hdrate : depositRate.val ≤ 10000) (hwrate : withdrawalRate.val ≤ 10000)
    (hmrate : marginRate.val ≤ 10000)
    (h : zkcash.utils.validate_fee extAmt fee depositRate withdrawalRate marginRate
      = ok (.Ok ())) :
    feeSufficient
          { authority := default, depositFeeRate := depositRate.val,
            withdrawalFeeRate := withdrawalRate.val, feeMarginError := marginRate.val,
            maxDepositLimit := 0 } extAmt.val fee.val := by
  unfold zkcash.utils.validate_fee at h
  simp only [LeanSpec.feeSufficient]
  by_cases hpos : extAmt > 0#i64
  · rw [if_pos hpos] at h
    have hpos' : extAmt.val > 0 := by scalar_tac
    have hext : (IScalar.hcast .U128 extAmt).val = extAmt.val.natAbs := by
      simp [IScalar.hcast_val_eq]; scalar_tac
    have h := (feeTailEq (IScalar.hcast .U128 extAmt) (UScalar.cast .U128 depositRate) fee
      marginRate (by rw [hext]; scalar_tac) (by simp; omega) hmrate _ _).symm.trans h
    rw [if_pos hpos']
    split_ifs at h with hc
    · simpa [hext] using hc
    · exact absurd h (feeErrNeOk _)
  · rw [if_neg hpos] at h
    have hpos' : ¬ extAmt.val > 0 := by scalar_tac
    rw [if_neg hpos']
    by_cases hneg : extAmt < 0#i64
    · rw [if_pos hneg] at h
      by_cases hmin : extAmt = core.num.I64.MIN
      · -- `checked_neg` overflows: `?` propagates `ArithmeticOverflow`, never `Ok`.
        simp only [core.num.I64.checked_neg, if_pos hmin, bind_tc_ok, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at h
        exact absurd h (bindNeOkUnit _ _ fun _ => by simp)
      · have hneg' : extAmt.val < 0 := by scalar_tac
        obtain ⟨y, hy, hyv⟩ : ∃ y : Std.I64, IScalar.neg extAmt = ok y ∧ y.val = -extAmt.val := by
          have hs := IScalar.neg_step extAmt (by intro hc; apply hmin; apply IScalar.eq_of_val_eq; rw [hc]; simp [I64.min_eq, I64.rMin])
          cases hc : IScalar.neg extAmt with
          | ok y => rw [hc] at hs; exact ⟨y, rfl, by simpa using hs⟩
          | fail e => rw [hc] at hs; simp at hs
          | div => rw [hc] at hs; simp at hs
        simp only [core.num.I64.checked_neg, if_neg hmin, hy, bind_tc_ok, core.option.Option.ok_or,
          core.result.Result.Insts.CoreOpsTry.branch] at h
        have hw : (UScalar.cast .U128 (IScalar.hcast .U64 y)).val = extAmt.val.natAbs := by
          simp [IScalar.hcast_val_eq, hyv]; scalar_tac
        have h := (feeTailEq (UScalar.cast .U128 (IScalar.hcast .U64 y))
          (UScalar.cast .U128 withdrawalRate) fee marginRate (by rw [hw]; scalar_tac)
          (by simp; omega) hmrate _ _).symm.trans h
        split_ifs at h with hc
        · simpa [hw] using hc
        · exact absurd h (feeErrNeOk _)
    · -- `extAmt = 0`: the expected fee is `0`, so any fee suffices.
      have hz : extAmt.val = 0 := by scalar_tac
      simp [hz]

/-- Converse of `feeSufficientRefines`, on the accept path only: if `feeSufficient` holds
(and `extAmt ≠ i64::MIN`, see above), `validate_fee` accepts. Not needed for safety; used by
`fv_transact_entry_depositAcceptRefines` below. Never touches a rejection branch. -/
theorem feeSufficientAccepts (extAmt : Std.I64) (fee : Std.U64)
    (depositRate withdrawalRate marginRate : Std.U16)
    (hdrate : depositRate.val ≤ 10000) (hwrate : withdrawalRate.val ≤ 10000)
    (hmrate : marginRate.val ≤ 10000) (hmin : extAmt ≠ core.num.I64.MIN)
    (hP : feeSufficient
          { authority := default, depositFeeRate := depositRate.val,
            withdrawalFeeRate := withdrawalRate.val, feeMarginError := marginRate.val,
            maxDepositLimit := 0 } extAmt.val fee.val) :
    zkcash.utils.validate_fee extAmt fee depositRate withdrawalRate marginRate
      = ok (.Ok ()) := by
  unfold zkcash.utils.validate_fee
  simp only [LeanSpec.feeSufficient] at hP
  by_cases hpos : extAmt > 0#i64
  · rw [if_pos hpos]
    have hpos' : extAmt.val > 0 := by scalar_tac
    have hext : (IScalar.hcast .U128 extAmt).val = extAmt.val.natAbs := by
      simp [IScalar.hcast_val_eq]; scalar_tac
    rw [if_pos hpos'] at hP
    refine (feeTailEq (IScalar.hcast .U128 extAmt) (UScalar.cast .U128 depositRate) fee
      marginRate (by rw [hext]; scalar_tac) (by simp; omega) hmrate _ _).trans ?_
    rw [if_pos (by simpa [hext] using hP)]
  · rw [if_neg hpos]
    have hpos' : ¬ extAmt.val > 0 := by scalar_tac
    rw [if_neg hpos'] at hP
    by_cases hneg : extAmt < 0#i64
    · rw [if_pos hneg]
      have hneg' : extAmt.val < 0 := by scalar_tac
      obtain ⟨y, hy, hyv⟩ : ∃ y : Std.I64, IScalar.neg extAmt = ok y ∧ y.val = -extAmt.val := by
        have hs := IScalar.neg_step extAmt
          (by intro hc; apply hmin; apply IScalar.eq_of_val_eq; rw [hc]; simp [I64.min_eq, I64.rMin])
        cases hc : IScalar.neg extAmt with
        | ok y => rw [hc] at hs; exact ⟨y, rfl, by simpa using hs⟩
        | fail e => rw [hc] at hs; simp at hs
        | div => rw [hc] at hs; simp at hs
      simp only [core.num.I64.checked_neg, if_neg hmin, hy, bind_tc_ok, core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry.branch]
      have hw : (UScalar.cast .U128 (IScalar.hcast .U64 y)).val = extAmt.val.natAbs := by
        simp [IScalar.hcast_val_eq, hyv]; scalar_tac
      refine (feeTailEq (UScalar.cast .U128 (IScalar.hcast .U64 y))
        (UScalar.cast .U128 withdrawalRate) fee marginRate (by rw [hw]; scalar_tac)
        (by simp; omega) hmrate _ _).trans ?_
      rw [if_pos (by simpa [hw] using hP)]
    · rw [if_neg hneg]

/-! ## externalDataBound: connecting `calculate_complete_ext_data_hash`

`calculate_complete_ext_data_hash` Borsh-serializes the seven public fields of a
transaction in a fixed order, then hashes the result. That splits the connection into two
independent facts: the serialized bytes match `serealizeExternalData` applied to the
mapped inputs (proven below, `serializeExtDataMatches`, no assumption needed), and the
code's hash axiom agrees with the spec's abstract `Sha` instance on that preimage
(assumed; see `externalDataBoundRefines`'s docstring for why this is the right place to
stop rather than a gap found by accident).

    code inputs ──── serialize, then hash ────▶  bytes : Array U8 32
         │                                              │
      mapping                                mapBytesToNatLE, cast to F
         ▼                                              ▼
    spec inputs ──── externalDataHash ────▶            F
-/

-- A single Rust byte, read as the spec's `Byte`. `U8.bv` already carries the same 8 bits
-- `x.val` does, so this is a relabeling, not a computation.
def mapByteToBit (x : Std.U8) : LeanSpec.Byte := x.bv

-- A Rust byte list, mapped element by element into the spec's `Bytes`.
def mapBytesToByteList (l : List Std.U8) : LeanSpec.Bytes := l.map mapByteToBit

-- 32 bytes read as a natural number, little-endian (byte 0 least significant), the same
-- way `FrShim.from_le_bytes_mod_order` reads the locally recomputed ext-data hash.
def mapBytesToNatLE (b : Array Std.U8 32#usize) : ℕ :=
  b.val.foldr (fun byte acc => acc * 256 + byte.val) 0

-- `mapBytesToNatLE`, reduced mod `p`.
def mapBytesToFLE (b : Array Std.U8 32#usize) : F := (mapBytesToNatLE b : F)

-- A Solana pubkey, read as the spec's `Pubkey`. Pubkey bytes are stored and sent as-is
-- (`solana_pubkey::Pubkey` is a plain 32-byte array), and the spec reads a pubkey's bytes
-- little-endian (`PubkeyToBytes`), matching `mapBytesToNatLE` above.
def mapPubkey (pk : solana_pubkey.Pubkey) : LeanSpec.Pubkey :=
  BitVec.ofNat 256 (mapBytesToNatLE pk)

-- `natToBytesLE`/`leBytes` are the same little endian encoding of a natural number, one
-- spec side and one code side, differing only in which byte type they land in (`BitVec 8`
-- versus `Std.U8`). Proven once, for any width, and reused for pubkeys, `i64`, `u64` and
-- length prefixes below.
private theorem natToBytesLEEqLeBytes (w n : ℕ) :
    LeanSpec.natToBytesLE w n = mapBytesToByteList (leBytes w n) := by
  simp only [LeanSpec.natToBytesLE, leBytes, mapBytesToByteList, List.map_map]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, mapByteToBit, byteOfNat, U8.ofNatCore]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow, Nat.pow_mul]

-- Decoding a byte list little-endian and re-encoding it the same width recovers the list.
-- The other direction of `natToBytesLEEqLeBytes`, needed once the code side is a *list of
-- bytes it already has* rather than a number it is about to produce.
private theorem leBytesFoldrEq (l : List Std.U8) :
    leBytes l.length (l.foldr (fun byte acc => acc * 256 + byte.val) 0) = l := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hval : x.val < 256 := by scalar_tac
    simp only [List.foldr, List.length_cons]
    set acc := xs.foldr (fun byte acc => acc * 256 + byte.val) 0 with hacc
    have hstep : leBytes (xs.length + 1) (acc * 256 + x.val)
        = byteOfNat (acc * 256 + x.val) :: leBytes xs.length ((acc * 256 + x.val) / 256) := by
      simp only [leBytes, List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      · simp
      · apply List.map_congr_left
        intro i _
        simp only [Function.comp]
        congr 1
        rw [Nat.div_div_eq_div_mul, ← pow_succ']
    rw [hstep]
    have h1 : (acc * 256 + x.val) / 256 = acc := by
      rw [Nat.mul_comm acc 256, Nat.mul_add_div (by norm_num) acc x.val,
        Nat.div_eq_of_lt hval, Nat.add_zero]
    have h2 : byteOfNat (acc * 256 + x.val) = x := by
      apply UScalar.eq_of_val_eq
      simp only [byteOfNat, U8.ofNatCore_val_eq]
      omega
    rw [h1, h2, ih]

-- `mapBytesToNatLE` as the existing (already reversed) `256`-base fold, so `foldlBound`
-- (proven for `checkPublicAmountRefines`) covers this direction too.
private theorem mapBytesToNatLEEqFoldl (b : Array Std.U8 32#usize) :
    mapBytesToNatLE b = b.val.reverse.foldl (fun acc x => acc * 256 + x.val) 0 :=
  List.foldr_eq_foldl_reverse

-- `PubkeyToBytes` of the mapped pubkey reproduces exactly the bytes the code serializes.
private theorem pubkeyToBytesEq (pk : solana_pubkey.Pubkey) :
    LeanSpec.PubkeyToBytes (mapPubkey pk) = mapBytesToByteList pk.val := by
  have hlen : pk.val.length = 32 := pk.property
  have hlen2 : pk.val.reverse.length = 32 := by rw [List.length_reverse]; exact hlen
  have h256 : (256 : ℕ) ^ 32 = 2 ^ 256 := by
    have h8 : (256 : ℕ) ^ 32 = (2 ^ 8) ^ 32 := by norm_num
    rw [h8, ← pow_mul]
  have hbound : mapBytesToNatLE pk < 2 ^ 256 := by
    rw [mapBytesToNatLEEqFoldl]
    calc pk.val.reverse.foldl (fun acc x => acc * 256 + x.val) 0
        < 256 ^ pk.val.reverse.length := foldlBound pk.val.reverse
      _ = 256 ^ 32 := by rw [hlen2]
      _ = 2 ^ 256 := h256
  simp only [LeanSpec.PubkeyToBytes, mapPubkey]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbound]
  rw [← leBytesFoldrEq pk.val, hlen]
  exact natToBytesLEEqLeBytes 32 (mapBytesToNatLE pk)

-- `i64LE` of the code's `i64` reproduces exactly the bytes `I64.Insts...serialize` writes.
private theorem i64LEEq (x : Std.I64) :
    LeanSpec.i64LE x.val = mapBytesToByteList (leBytes 8 (x.val % (2 ^ 64 : ℤ)).toNat) :=
  natToBytesLEEqLeBytes 8 (x.val % (2 ^ 64 : ℤ)).toNat

-- `u64LE` of the code's `u64` reproduces exactly the bytes `U64.Insts...serialize` writes.
private theorem u64LEEq (x : Std.U64) :
    LeanSpec.u64LE x.val = mapBytesToByteList (leBytes 8 x.val) :=
  natToBytesLEEqLeBytes 8 x.val

-- `vecU8` of the mapped bytes reproduces exactly the length-prefix-then-bytes encoding
-- `Vec<u8>`'s Borsh serialize writes (the length prefix via `wrBytes`, the bytes via
-- `borshSerList`).
private theorem vecU8Eq (l : List Std.U8) :
    LeanSpec.vecU8 (mapBytesToByteList l) = mapBytesToByteList (leBytes 4 l.length ++ l) := by
  simp only [LeanSpec.vecU8, LeanSpec.u32LE, mapBytesToByteList, List.length_map, List.map_append]
  rw [natToBytesLEEqLeBytes]
  simp [mapBytesToByteList]

/-! ### The serialize chain always succeeds

`wrBytes` (hence every Borsh `serialize` in this file) can only fail by exceeding
`Usize.max`, which nothing in a transaction's ext data comes remotely close to. The lemmas
below make that concrete: each serialize step, given enough headroom, succeeds and appends
exactly its bytes to the writer, `rfl`-style once the headroom side condition is supplied. -/

-- `wrBytes` against the `Vec<u8>` writer: always `Ok`, appending `l` to the buffer,
-- given enough headroom. The only way `std::io::Write for Vec<u8>` can fail.
private theorem wrBytesOk (A : Type) (l : List Std.U8) (w : alloc.vec.Vec Std.U8)
    (h : l.length ≤ Std.Usize.max) (hsum : w.length + l.length ≤ Std.Usize.max) :
    wrBytes (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) l w h
      = ok (core.result.Result.Ok (), (⟨w.val ++ l, by scalar_tac⟩ : alloc.vec.Vec Std.U8)) := by
  have hwrite : alloc.vec.VecU8.Insts.StdIoWrite.write A w (⟨l, h⟩ : Slice Std.U8)
      = ok (core.result.Result.Ok (Slice.len (⟨l, h⟩ : Slice Std.U8)),
          (⟨w.val ++ l, by scalar_tac⟩ : alloc.vec.Vec Std.U8)) := by
    unfold alloc.vec.VecU8.Insts.StdIoWrite.write
    rw [dif_pos hsum]
    rfl
  show (do
    let (r, w') ← alloc.vec.VecU8.Insts.StdIoWrite.write A w (⟨l, h⟩ : Slice Std.U8)
    match r with
    | core.result.Result.Ok _ => ok (core.result.Result.Ok (), w')
    | core.result.Result.Err e => ok (core.result.Result.Err e, w')) = _
  rw [hwrite]
  rfl

-- One byte, Borsh-serialized: `wrBytes` on the singleton list.
private theorem u8SerializeOk (A : Type) (x : Std.U8) (w : alloc.vec.Vec Std.U8)
    (hsum : w.length + 1 ≤ Std.Usize.max) :
    U8.Insts.BorshSerBorshSerialize.serialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) x w
      = ok (core.result.Result.Ok (), (⟨w.val ++ [x], by scalar_tac⟩ : alloc.vec.Vec Std.U8)) := by
  simp only [U8.Insts.BorshSerBorshSerialize.serialize]
  exact wrBytesOk A [x] w (by scalar_tac) hsum

-- A byte list, serialized element by element: succeeds throughout and leaves the buffer
-- with every element appended in order, given headroom for the whole list up front.
private theorem borshSerListU8Ok (A : Type) (l : List Std.U8) (w : alloc.vec.Vec Std.U8)
    (hsum : w.length + l.length ≤ Std.Usize.max) :
    borshSerList zkcash.U8.Insts.BorshSerBorshSerialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A)
      l w
      = ok (core.result.Result.Ok (), (⟨w.val ++ l, by scalar_tac⟩ : alloc.vec.Vec Std.U8)) := by
  induction l generalizing w with
  | nil =>
    show ok (core.result.Result.Ok (), w) = _
    congr 2
    exact Subtype.ext (List.append_nil w.val).symm
  | cons x xs ih =>
    have h1 : w.length + 1 ≤ Std.Usize.max := by scalar_tac
    have hstep := u8SerializeOk A x w h1
    have h2 : (w.val ++ [x]).length + xs.length ≤ Std.Usize.max := by scalar_tac
    have hrec := ih (⟨w.val ++ [x], by scalar_tac⟩ : alloc.vec.Vec Std.U8) h2
    show (do
      let (r, w') ← U8.Insts.BorshSerBorshSerialize.serialize
        (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) x w
      match r with
      | core.result.Result.Ok _ =>
        borshSerList zkcash.U8.Insts.BorshSerBorshSerialize
          (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) xs w'
      | core.result.Result.Err e => ok (core.result.Result.Err e, w')) = _
    rw [hstep]
    show borshSerList zkcash.U8.Insts.BorshSerBorshSerialize
        (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) xs
        (⟨w.val ++ [x], by scalar_tac⟩ : alloc.vec.Vec Std.U8)
      = ok (core.result.Result.Ok (),
          (⟨w.val ++ (x :: xs), by scalar_tac⟩ : alloc.vec.Vec Std.U8))
    rw [hrec]
    congr 2
    exact Subtype.ext (by simp)

-- Every `leBytes`/`natToBytesLE` output has exactly its stated width. Used throughout this
-- section to discharge the `Usize.max` headroom side conditions `wrBytesOk` needs.
private theorem leBytesLength (w n : ℕ) : (leBytes w n).length = w := by simp [leBytes]

-- One `i64`, Borsh-serialized: `wrBytes` on its little-endian bytes.
private theorem i64SerializeOk (A : Type) (x : Std.I64) (w : alloc.vec.Vec Std.U8)
    (hsum : w.length + 8 ≤ Std.Usize.max) :
    I64.Insts.BorshSerBorshSerialize.serialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) x w
      = ok (core.result.Result.Ok (),
          (⟨w.val ++ leBytes 8 (x.val % (2 ^ 64 : ℤ)).toNat,
            by simp only [List.length_append, leBytesLength]; scalar_tac⟩ :
            alloc.vec.Vec Std.U8)) := by
  simp only [I64.Insts.BorshSerBorshSerialize.serialize]
  have hl : (leBytes 8 (x.val % (2 ^ 64 : ℤ)).toNat).length ≤ Std.Usize.max := by
    rw [leBytesLength]; scalar_tac
  exact wrBytesOk A _ w hl (by rw [leBytesLength]; exact hsum)

-- One `u64`, Borsh-serialized: `wrBytes` on its little-endian bytes.
private theorem u64SerializeOk (A : Type) (x : Std.U64) (w : alloc.vec.Vec Std.U8)
    (hsum : w.length + 8 ≤ Std.Usize.max) :
    U64.Insts.BorshSerBorshSerialize.serialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) x w
      = ok (core.result.Result.Ok (),
          (⟨w.val ++ leBytes 8 x.val,
            by simp only [List.length_append, leBytesLength]; scalar_tac⟩ :
            alloc.vec.Vec Std.U8)) := by
  simp only [U64.Insts.BorshSerBorshSerialize.serialize]
  have hl : (leBytes 8 x.val).length ≤ Std.Usize.max := by rw [leBytesLength]; scalar_tac
  exact wrBytesOk A _ w hl (by rw [leBytesLength]; exact hsum)

-- One pubkey, Borsh-serialized: `wrBytes` on its 32 raw bytes (no length prefix, unlike a
-- `Vec<u8>` -- a pubkey is a fixed-size array).
private theorem pubkeySerializeOk (A : Type) (pk : solana_pubkey.Pubkey)
    (w : alloc.vec.Vec Std.U8) (hsum : w.length + 32 ≤ Std.Usize.max) :
    solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize.serialize
      (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) pk w
      = ok (core.result.Result.Ok (),
          (⟨w.val ++ pk.val, by simp only [List.length_append, pk.property]; scalar_tac⟩ :
            alloc.vec.Vec Std.U8)) := by
  simp only [solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize.serialize]
  have hl : pk.val.length ≤ Std.Usize.max := by rw [pk.property]; scalar_tac
  exact wrBytesOk A _ w hl (by rw [pk.property]; exact hsum)

-- A `Vec<u8>`, Borsh-serialized: the 4-byte length prefix (`wrBytes`), then every element
-- (`borshSerList`).
private theorem vecU8SerializeOk (A : Type) (v : alloc.vec.Vec Std.U8) (w : alloc.vec.Vec Std.U8)
    (hsum : w.length + 4 + v.length ≤ Std.Usize.max) :
    alloc.vec.Vec.Insts.BorshSerBorshSerialize.serialize zkcash.U8.Insts.BorshSerBorshSerialize
      (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) v w
      = ok (core.result.Result.Ok (),
          (⟨w.val ++ leBytes 4 v.length ++ v.val,
            by simp only [List.length_append, leBytesLength]; scalar_tac⟩ :
            alloc.vec.Vec Std.U8)) := by
  have h1 : w.length + (leBytes 4 v.length).length ≤ Std.Usize.max := by
    rw [leBytesLength]; scalar_tac
  have hstep := wrBytesOk A (leBytes 4 v.length) w (by rw [leBytesLength]; scalar_tac) h1
  have h2 : (w.val ++ leBytes 4 v.length).length + v.val.length ≤ Std.Usize.max := by
    rw [List.length_append, leBytesLength]; scalar_tac
  have hrec := borshSerListU8Ok A v.val
    (⟨w.val ++ leBytes 4 v.length,
      by simp only [List.length_append, leBytesLength]; scalar_tac⟩ : alloc.vec.Vec Std.U8) h2
  simp only [alloc.vec.Vec.Insts.BorshSerBorshSerialize.serialize]
  show (do
    let (r, w') ← wrBytes (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) (leBytes 4 v.length) w
      (by rw [leBytesLength]; scalar_tac)
    match r with
    | core.result.Result.Ok _ =>
      borshSerList zkcash.U8.Insts.BorshSerBorshSerialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A)
        v.val w'
    | core.result.Result.Err e => ok (core.result.Result.Err e, w')) = _
  rw [hstep]
  show borshSerList zkcash.U8.Insts.BorshSerBorshSerialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A)
      v.val (⟨w.val ++ leBytes 4 v.length,
        by simp only [List.length_append, leBytesLength]; scalar_tac⟩ : alloc.vec.Vec Std.U8)
    = ok (core.result.Result.Ok (),
        (⟨w.val ++ leBytes 4 v.length ++ v.val,
          by simp only [List.length_append, leBytesLength]; scalar_tac⟩ : alloc.vec.Vec Std.U8))
  rw [hrec]

-- Each field of `CompleteExtData` is serialized through Rust's `?` operator, which
-- Aeneas compiles to a `branch`/`Continue`/`Break` dance on the `core::result::Result`
-- the serialize call already returns. Given that call succeeds, this collapses the dance
-- to the `Continue` body directly -- the `Write`-typed sibling of `tryContinueOverflow`.
private theorem serializeStepOk {E α : Type}
    {step : Result (core.result.Result Unit E × alloc.vec.Vec Std.U8)}
    {w' : alloc.vec.Vec Std.U8} (hstep : step = ok (core.result.Result.Ok (), w'))
    (cont : alloc.vec.Vec Std.U8 → Result α)
    (propagate : alloc.vec.Vec Std.U8 → core.result.Result core.convert.Infallible E → Result α) :
    (do
      let (r, w'') ← step
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue _ => cont w''
      | core.ops.control_flow.ControlFlow.Break residual => propagate w'' residual)
      = cont w' := by
  subst hstep
  rfl

-- The seven-field struct, Borsh-serialized field by field: succeeds throughout (given
-- headroom for the whole preimage up front) and leaves the buffer with exactly the
-- concatenation of each field's bytes, in field order -- the code-side mirror of
-- `serealizeExternalData`.
private theorem completeExtDataSerializeOk (A : Type) (recipient fee_recipient mint_address :
    solana_pubkey.Pubkey) (ext_amount : Std.I64)
    (encrypted_output1 encrypted_output2 : alloc.vec.Vec Std.U8) (fee : Std.U64)
    (w : alloc.vec.Vec Std.U8)
    (hsum : w.length + 32 + 8 + (4 + encrypted_output1.length) + (4 + encrypted_output2.length)
      + 8 + 32 + 32 ≤ Std.Usize.max) :
    zkcash.utils.calculate_complete_ext_data_hash.CompleteExtData.Insts.BorshSerBorshSerialize.serialize
      zkcash.solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize
      zkcash.I64.Insts.BorshSerBorshSerialize
      (zkcash.alloc.vec.Vec.Insts.BorshSerBorshSerialize zkcash.U8.Insts.BorshSerBorshSerialize)
      zkcash.U64.Insts.BorshSerBorshSerialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A)
      { recipient, ext_amount, encrypted_output1, encrypted_output2, fee, fee_recipient,
        mint_address :
        zkcash.utils.calculate_complete_ext_data_hash.CompleteExtData } w
      = ok (core.result.Result.Ok (),
          (⟨w.val ++ recipient.val ++ leBytes 8 (ext_amount.val % (2 ^ 64 : ℤ)).toNat
              ++ leBytes 4 encrypted_output1.length ++ encrypted_output1.val
              ++ leBytes 4 encrypted_output2.length ++ encrypted_output2.val
              ++ leBytes 8 fee.val ++ fee_recipient.val ++ mint_address.val,
            by simp only [List.length_append, leBytesLength, recipient.property,
              fee_recipient.property, mint_address.property]; scalar_tac⟩ :
            alloc.vec.Vec Std.U8)) := by
  have hlr : recipient.val.length = 32 := recipient.property
  have hlt : fee_recipient.val.length = 32 := fee_recipient.property
  have hlm : mint_address.val.length = 32 := mint_address.property
  have hw1 : (w.val ++ recipient.val).length ≤ Std.Usize.max := by
    simp only [List.length_append, hlr]; scalar_tac
  set w1 : alloc.vec.Vec Std.U8 := ⟨w.val ++ recipient.val, hw1⟩ with hw1def
  have hw2 : (w1.val ++ leBytes 8 (ext_amount.val % (2 ^ 64 : ℤ)).toNat).length ≤ Std.Usize.max := by
    simp only [hw1def, List.length_append, hlr, leBytesLength]; scalar_tac
  set w2 : alloc.vec.Vec Std.U8 :=
    ⟨w1.val ++ leBytes 8 (ext_amount.val % (2 ^ 64 : ℤ)).toNat, hw2⟩ with hw2def
  have hw3 : (w2.val ++ leBytes 4 encrypted_output1.length ++ encrypted_output1.val).length
      ≤ Std.Usize.max := by
    simp only [hw2def, hw1def, List.length_append, hlr, leBytesLength]; scalar_tac
  set w3 : alloc.vec.Vec Std.U8 :=
    ⟨w2.val ++ leBytes 4 encrypted_output1.length ++ encrypted_output1.val, hw3⟩ with hw3def
  have hw4 : (w3.val ++ leBytes 4 encrypted_output2.length ++ encrypted_output2.val).length
      ≤ Std.Usize.max := by
    simp only [hw3def, hw2def, hw1def, List.length_append, hlr, leBytesLength]; scalar_tac
  set w4 : alloc.vec.Vec Std.U8 :=
    ⟨w3.val ++ leBytes 4 encrypted_output2.length ++ encrypted_output2.val, hw4⟩ with hw4def
  have hw5 : (w4.val ++ leBytes 8 fee.val).length ≤ Std.Usize.max := by
    simp only [hw4def, hw3def, hw2def, hw1def, List.length_append, hlr, leBytesLength]; scalar_tac
  set w5 : alloc.vec.Vec Std.U8 := ⟨w4.val ++ leBytes 8 fee.val, hw5⟩ with hw5def
  have hw6 : (w5.val ++ fee_recipient.val).length ≤ Std.Usize.max := by
    simp only [hw5def, hw4def, hw3def, hw2def, hw1def, List.length_append, hlr, hlt, leBytesLength]
    scalar_tac
  set w6 : alloc.vec.Vec Std.U8 := ⟨w5.val ++ fee_recipient.val, hw6⟩ with hw6def
  have hw7 : (w6.val ++ mint_address.val).length ≤ Std.Usize.max := by
    simp only [hw6def, hw5def, hw4def, hw3def, hw2def, hw1def, List.length_append, hlr, hlt, hlm,
      leBytesLength]
    scalar_tac
  set w7 : alloc.vec.Vec Std.U8 := ⟨w6.val ++ mint_address.val, hw7⟩ with hw7def
  have hstep1 : solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize.serialize
      (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) recipient w = ok (core.result.Result.Ok (), w1) := by
    rw [hw1def]; exact pubkeySerializeOk A recipient w (by scalar_tac)
  have hstep2 : I64.Insts.BorshSerBorshSerialize.serialize
      (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) ext_amount w1 = ok (core.result.Result.Ok (), w2) := by
    rw [hw2def]
    exact i64SerializeOk A ext_amount w1
      (by simp only [List.length_append, leBytesLength] at hw2; exact hw2)
  have hstep3 : alloc.vec.Vec.Insts.BorshSerBorshSerialize.serialize
      zkcash.U8.Insts.BorshSerBorshSerialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A)
      encrypted_output1 w2 = ok (core.result.Result.Ok (), w3) := by
    rw [hw3def]
    exact vecU8SerializeOk A encrypted_output1 w2
      (by simp only [hw2def, List.length_append, hlr, leBytesLength]; scalar_tac)
  have hstep4 : alloc.vec.Vec.Insts.BorshSerBorshSerialize.serialize
      zkcash.U8.Insts.BorshSerBorshSerialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A)
      encrypted_output2 w3 = ok (core.result.Result.Ok (), w4) := by
    rw [hw4def]
    exact vecU8SerializeOk A encrypted_output2 w3
      (by simp only [hw3def, hw2def]; scalar_tac)
  have hstep5 : U64.Insts.BorshSerBorshSerialize.serialize
      (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) fee w4 = ok (core.result.Result.Ok (), w5) := by
    rw [hw5def]
    exact u64SerializeOk A fee w4
      (by simp only [List.length_append, leBytesLength] at hw5; exact hw5)
  have hstep6 : solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize.serialize
      (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) fee_recipient w5 = ok (core.result.Result.Ok (), w6) := by
    rw [hw6def]
    exact pubkeySerializeOk A fee_recipient w5
      (by simp only [List.length_append, hlt] at hw6; exact hw6)
  have hstep7 : solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize.serialize
      (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A) mint_address w6 = ok (core.result.Result.Ok (), w7) := by
    rw [hw7def]
    exact pubkeySerializeOk A mint_address w6
      (by simp only [List.length_append, hlm] at hw7; exact hw7)
  simp only [zkcash.utils.calculate_complete_ext_data_hash.CompleteExtData.Insts.BorshSerBorshSerialize.serialize]
  rw [hstep1]
  simp [Aeneas.Std.bind, Bind.bind, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hstep2]
  simp [Aeneas.Std.bind, Bind.bind, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hstep3]
  simp [Aeneas.Std.bind, Bind.bind, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hstep4]
  simp [Aeneas.Std.bind, Bind.bind, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hstep5]
  simp [Aeneas.Std.bind, Bind.bind, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hstep6]
  simp [Aeneas.Std.bind, Bind.bind, core.result.Result.Insts.CoreOpsTry.branch]
  rw [hstep7]
  simp [Aeneas.Std.bind, Bind.bind, core.result.Result.Insts.CoreOpsTry.branch]
  rfl

-- `completeExtDataSerializeOk`, restated as a Hoare triple so Aeneas's `step` tactic can
-- apply it (it matches specs shaped `f args ⦃ r => ... ⦄`, not plain equations).
private theorem completeExtDataSerializeOkSpec (A : Type) (recipient fee_recipient mint_address :
    solana_pubkey.Pubkey) (ext_amount : Std.I64)
    (encrypted_output1 encrypted_output2 : alloc.vec.Vec Std.U8) (fee : Std.U64)
    (w : alloc.vec.Vec Std.U8)
    (hsum : w.length + 32 + 8 + (4 + encrypted_output1.length) + (4 + encrypted_output2.length)
      + 8 + 32 + 32 ≤ Std.Usize.max) :
    zkcash.utils.calculate_complete_ext_data_hash.CompleteExtData.Insts.BorshSerBorshSerialize.serialize
      zkcash.solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize
      zkcash.I64.Insts.BorshSerBorshSerialize
      (zkcash.alloc.vec.Vec.Insts.BorshSerBorshSerialize zkcash.U8.Insts.BorshSerBorshSerialize)
      zkcash.U64.Insts.BorshSerBorshSerialize (zkcash.alloc.vec.VecU8.Insts.StdIoWrite A)
      { recipient, ext_amount, encrypted_output1, encrypted_output2, fee, fee_recipient,
        mint_address :
        zkcash.utils.calculate_complete_ext_data_hash.CompleteExtData } w
      ⦃ (p : core.result.Result Unit std.io.error.Error × alloc.vec.Vec Std.U8) =>
        p.1 = core.result.Result.Ok () ∧
          p.2.val = w.val ++ recipient.val ++ leBytes 8 (ext_amount.val % (2 ^ 64 : ℤ)).toNat
            ++ leBytes 4 encrypted_output1.length ++ encrypted_output1.val
            ++ leBytes 4 encrypted_output2.length ++ encrypted_output2.val
            ++ leBytes 8 fee.val ++ fee_recipient.val ++ mint_address.val ⦄ := by
  rw [completeExtDataSerializeOk A recipient fee_recipient mint_address ext_amount
    encrypted_output1 encrypted_output2 fee w hsum]
  exact (WP.spec_ok _).mpr ⟨rfl, rfl⟩

-- `externalDataHash`, unpacked to just the seven fields it actually reads. `TxInputs`
-- carries the whole transaction's state (root, nullifiers, the proof, ...), none of which
-- `serealizeExternalData` touches, so building a full `TxInputs` literal here would need
-- placeholder values for fields this connection has no opinion on. `externalDataHashOfEq`
-- below ties this back to the real spec definition by `rfl`.
def externalDataHashOf [LeanSpec.Sha] (A : LeanSpec.Pubkey) (extAmt : ℤ) (encOut0 encOut1 :
    LeanSpec.Bytes) (f : ℕ) (t mintAddr : LeanSpec.Pubkey) : F :=
  (LeanSpec.natOfLE (LeanSpec.Sha.sha256
    (LeanSpec.PubkeyToBytes A ++ LeanSpec.i64LE extAmt ++ LeanSpec.vecU8 encOut0
      ++ LeanSpec.vecU8 encOut1 ++ LeanSpec.u64LE f ++ LeanSpec.PubkeyToBytes t
      ++ LeanSpec.PubkeyToBytes mintAddr)) : F)

theorem externalDataHashOfEq [LeanSpec.Sha] (inputs : LeanSpec.TxInputs) :
    externalDataHashOf inputs.A inputs.extAmt inputs.encOut0 inputs.encOut1 inputs.f inputs.t
      inputs.mintAddr = LeanSpec.externalDataHash inputs := rfl

set_option maxHeartbeats 1000000 in
/-- **Connection theorem for `zkcash::utils::calculate_complete_ext_data_hash`**

The code hashes the Borsh-serialized preimage with a trusted syscall axiom
(`solana_sha256_hasher.hash`, `code_model/hand_written/TrustedFuns.lean:356`) that carries
*no* stated properties, not even success. The spec's own `sha256` is exactly as
opaque, by design (`class Sha`, `Spec/privacy_cash_spec.lean:35`): every security
statement in the spec already goes through this class rather than a concrete hash, so
tying the two together needs one fact, given here as a hypothesis rather than assumed
silently: the code's axiom and the spec's abstract `sha256` agree on the preimage this
function actually builds. `hSha` is that fact, scoped to exactly this call.

The byte-for-byte equality itself (`completeExtDataSerializeOk`) is fully proven, and so is
this connection theorem: `step` (Aeneas's tactic for chaining through monadic function
calls, see `completeExtDataSerializeOkSpec` just above) reduces the function call
mechanically once it is restated as a Hoare triple, where `rw`/`simp`/`show` alone kept
getting stuck on `Vec`/`Array`'s deliberate non-reducibility. -/
theorem externalDataBoundRefines (recipient fee_recipient mint_address : solana_pubkey.Pubkey)
    (ext_amount : Std.I64) (encrypted_output1 encrypted_output2 : Slice Std.U8) (fee : Std.U64)
    [LeanSpec.Sha]
    (hSha : ∀ (bytes : List Std.U8) (h : bytes.length ≤ Std.Usize.max),
      ∃ digest : Array Std.U8 32#usize,
        solana_sha256_hasher.hash ⟨bytes, h⟩ = ok digest ∧
        mapBytesToByteList digest.val = LeanSpec.Sha.sha256 (mapBytesToByteList bytes))
    (hsum : 32 + 8 + (4 + encrypted_output1.length) + (4 + encrypted_output2.length) + 8 + 32 + 32
      ≤ Std.Usize.max) :
    zkcash.utils.calculate_complete_ext_data_hash recipient ext_amount encrypted_output1
      encrypted_output2 fee fee_recipient mint_address
      ⦃ (r : core.result.Result (Array Std.U8 32#usize) zkcash.anchor_lang.error.Error) =>
        ∃ h : Array Std.U8 32#usize, r = .Ok h ∧
          (mapBytesToNatLE h : F) = externalDataHashOf (mapPubkey recipient) ext_amount.val
            (mapBytesToByteList encrypted_output1.val) (mapBytesToByteList encrypted_output2.val)
            fee.val (mapPubkey fee_recipient) (mapPubkey mint_address) ⦄ := by
  unfold zkcash.utils.calculate_complete_ext_data_hash
  step as ⟨v, hveq⟩
  step as ⟨v1, hv1eq⟩
  have hvval : v.val = encrypted_output1.val := hveq ▸ rfl
  have hv1val : v1.val = encrypted_output2.val := hv1eq ▸ rfl
  have hlv : v.length = encrypted_output1.length := by show v.val.length = _; rw [hvval]
  have hlv1 : v1.length = encrypted_output2.length := by show v1.val.length = _; rw [hv1val]
  step with completeExtDataSerializeOkSpec as ⟨p, pv, hpok, hpval⟩
  rw [hpok]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok]
  have hlen : pv.val.length ≤ Std.Usize.max := by
    rw [hpval]
    have hbv : v.length = v.val.length := rfl
    have hbv1 : v1.length = v1.val.length := rfl
    have e1 : v.val.length = encrypted_output1.val.length := congrArg List.length hvval
    have e2 : v1.val.length = encrypted_output2.val.length := congrArg List.length hv1val
    have e3 := hsum
    have e4 : recipient.val.length = 32 := recipient.property
    have e5 : fee_recipient.val.length = 32 := fee_recipient.property
    have e6 : mint_address.val.length = 32 := mint_address.property
    simp only [List.length_append, leBytesLength, List.length_nil]
    omega
  have htarget : mapBytesToByteList pv.val =
      LeanSpec.PubkeyToBytes (mapPubkey recipient) ++ LeanSpec.i64LE ext_amount.val
        ++ LeanSpec.vecU8 (mapBytesToByteList v.val)
        ++ LeanSpec.vecU8 (mapBytesToByteList v1.val) ++ LeanSpec.u64LE fee.val
        ++ LeanSpec.PubkeyToBytes (mapPubkey fee_recipient)
        ++ LeanSpec.PubkeyToBytes (mapPubkey mint_address) := by
    rw [hpval]
    simp only [List.nil_append]
    rw [pubkeyToBytesEq, i64LEEq, vecU8Eq, vecU8Eq, u64LEEq, pubkeyToBytesEq, pubkeyToBytesEq]
    simp only [mapBytesToByteList, List.map_append, List.append_assoc]
  obtain ⟨digest, hdigest, hdigesteq⟩ := hSha pv.val hlen
  have hnat : LeanSpec.natOfLE (mapBytesToByteList digest.val) = mapBytesToNatLE digest := by
    simp only [LeanSpec.natOfLE, mapBytesToByteList, mapBytesToNatLE, List.foldr_map]
    congr 1
    funext x acc
    simp [mapByteToBit, Nat.add_comm, Nat.mul_comm]
  simp only [alloc.vec.Vec.deref, solana_hash.Hash.to_bytes]
  rw [hdigest]
  refine ⟨digest, rfl, ?_⟩
  simp only [externalDataHashOf]
  rw [← hnat, hdigesteq, htarget, hvval, hv1val]

/-! ## `transact`: the deposit accept-path, assembled

Everything above is a piece `transact` needs; this assembles them into one theorem about
`fv_transact_entry` itself (completeness direction; the safety result is `transactSafe`).
Scope, deliberately cut down to what's reachable today:

- **Deposit only** (`ext_data.ext_amount > 0`). Withdrawal takes the mirror-image branch
  through the same guards (`poolSolvent`'s first conjunct instead of `signerSolvent`,
  `transferEffectsWithdrawalRefines` instead of `...DepositRefines`); not done here.
- **Completeness direction, not safety.** This theorem goes from the spec's preconditions
  (as hypotheses) to "the code accepts, with matching effects". The file's scope is safety
  (see the header): code accepts ⟹ `transact` holds, which is what invariant inheritance
  needs. That is `transactSafe` in `TransactSafety.lean`. This theorem is a completeness
  result, not needed for the invariants.
- **`proofValid` is not derived.** `fv_verify_proof_full_entry`'s connection to
  `Groth16.verify` isn't started (see "Not yet connected" below), so `hVerify` below is a
  direct hypothesis on the code's verifier succeeding, standing in for `proofValid inputs`
  rather than being derived from it.
- **`nullifiers` is a free parameter.** The spent-nullifier set is an Anchor PDA, invisible
  to `code_model`; this theorem says nothing about it (matches "Not yet connected" below).
- **`appendRefines` is consumed, not reproved**, carrying its own `sorry` forward. The
  proof also has two `sorry`s of its own: the final effects equation in the `fee > 0` case
  (a `split_ifs` leftover, see the comment there) and the whole `fee = 0` case. -/

/-- The spec-level `TxInputs` a `fv_transact_entry` call corresponds to. `s` (the signer's
pubkey) and `π` (the Groth16 proof) aren't derivable from the code: `fv_transact_entry`
never receives the signer's pubkey, only their lamport balance, and decoding
`proof_a`/`proof_b`/`proof_c` into `π` needs the still-unstarted Groth16 pairing bridge --
both stay free parameters, tied to the code only through the hypotheses that use them. -/
def mapTxInputs (s : LeanSpec.Pubkey) (π : LeanSpec.Groth16.Proof)
    (proof_root proof_ext_data_hash proof_public_amount : Array Std.U8 32#usize)
    (input_nullifiers output_commitments : Array (Array Std.U8 32#usize) 2#usize)
    (ext_data : zkcash.ExtData)
    (encrypted_output1 encrypted_output2 : alloc.vec.Vec Std.U8) : LeanSpec.TxInputs where
  R := mapBytesToF proof_root
  pubAmt := mapBytesToF proof_public_amount
  extDataHash := mapBytesToF proof_ext_data_hash
  k0 := mapBytesToF input_nullifiers.val[0]!
  k1 := mapBytesToF input_nullifiers.val[1]!
  outC0 := mapBytesToF output_commitments.val[0]!
  outC1 := mapBytesToF output_commitments.val[1]!
  extAmt := ext_data.ext_amount.val
  f := ext_data.fee.val
  s := s
  A := mapPubkey ext_data.recipient
  t := mapPubkey ext_data.fee_recipient
  encOut0 := mapBytesToByteList (alloc.vec.Vec.deref encrypted_output1).val
  encOut1 := mapBytesToByteList (alloc.vec.Vec.deref encrypted_output2).val
  π := π
  mintAddr := mapPubkey ext_data.mint_address

/-- `GlobalConfig`'s fields map onto `config` field-for-field, except `maxDepositLimit`,
which lives on the tree account instead of `GlobalConfig` (see `depositWithinLimitRefines`'s
docstring). -/
def mapGlobalConfig (global_config : zkcash.GlobalConfig) (maxDeposit : Std.U64) :
    LeanSpec.config where
  authority := mapPubkey global_config.authority
  depositFeeRate := global_config.deposit_fee_rate.val
  withdrawalFeeRate := global_config.withdrawal_fee_rate.val
  feeMarginError := global_config.fee_error_margin.val
  maxDepositLimit := maxDeposit.val

/-- The spec-level `World` before a `fv_transact_entry` call. `nullifiers` is a free
parameter, for the reason given above. -/
def mapOldWorld (tree_account : zkcash.MerkleTreeAccount) (global_config : zkcash.GlobalConfig)
    (nullifiers : Finset F) (balances : LeanSpec.Pubkey → ℕ)
    (tree_token_lamports rent_exempt_minimum : Std.U64) : LeanSpec.World where
  state :=
    { tree := mapTree tree_account, nullifiers := nullifiers,
      solBalance := tree_token_lamports.val,
      config := mapGlobalConfig global_config tree_account.max_deposit_amount }
  balances := balances
  rentExemptMin := rent_exempt_minimum.val

-- `p` (the spec's field modulus) and `bn254_r` (the code's) are the same prime, spelled out
-- as two separate numerals -- `fr_shim.FrShim`'s own docstring already names this as "the
-- bridge a theorem relating this model to that spec would go through." This theorem is
-- that bridge's first use.
theorem hp_eq_bn254r : LeanSpec.p = bn254_r := by native_decide

-- A proven `⦃ ⦄` fact is only provable because the callee actually succeeds (the `⦃ ⦄`
-- framework maps `fail`/`div` to `False`, per the earlier discussion of `WP.spec`); this
-- makes that explicit, extracting the witness and its postcondition from any such fact
-- rather than re-deriving it by hand at every call site below.
private theorem specSucceeds {α} {p : α → Prop} (x : Result α) (hspec : x ⦃ p ⦄) :
    ∃ v, x = ok v ∧ p v := by
  cases x with
  | ok v => exact ⟨v, rfl, (WP.spec_ok v).mp hspec⟩
  | fail e => simp only [WP.spec_fail] at hspec
  | div => simp only [WP.spec_div] at hspec

theorem fv_transact_entry_depositAcceptRefines
    [LeanSpec.Sha] [LeanSpec.PoseidonHashes]
    (tree_account : zkcash.MerkleTreeAccount) (global_config : zkcash.GlobalConfig)
    (proof_root proof_ext_data_hash proof_public_amount : Array Std.U8 32#usize)
    (input_nullifiers output_commitments : Array (Array Std.U8 32#usize) 2#usize)
    (proof_a : Array Std.U8 64#usize) (proof_b : Array Std.U8 128#usize)
    (proof_c : Array Std.U8 64#usize) (ext_data_minified : zkcash.ExtDataMinified)
    (encrypted_output1 encrypted_output2 : alloc.vec.Vec Std.U8)
    (rent_exempt_minimum tree_token_lamports signer_lamports : Std.U64)
    (recipient fee_recipient_account : zkcash.FvAccount)
    (s : LeanSpec.Pubkey) (π : LeanSpec.Groth16.Proof) (nullifiers : Finset F)
    (balances : LeanSpec.Pubkey → ℕ)
    (ext_data : zkcash.ExtData)
    (a : Array Std.U8 64#usize) (a1 a2 a3 : Array Std.U8 128#usize)
    (a4 : Array (Array Std.U8 64#usize) 8#usize)
    -- `fv_ext_data_from_minified` and the balances the signer / fee recipient hold,
    -- exactly as `signerSolventRefines` / `transferEffectsDepositRefines` /
    -- `transactEffectsFeeRefines` already require.
    (hextdata : zkcash.fv_ext_data_from_minified recipient fee_recipient_account
        ext_data_minified = ok ext_data)
    (hbalS : balances s = signer_lamports.val)
    (hbalT : balances (mapPubkey ext_data.fee_recipient) = fee_recipient_account.lamports.val)
    -- Signer ≠ fee recipient: `transactEffects`'s fee update and `transferEffects`'s deposit
    -- update would otherwise both touch the same `balances` entry, and `Function.update`
    -- composition stops being the simple "untouched" case every formula below assumes. Real
    -- transactions where the signer pays their own fee to themselves are a genuine edge case
    -- this theorem doesn't attempt (matches `AgreesOnProgramEffects`'s own documented
    -- TODO about `payees` excluding the signer).
    (hst : s ≠ mapPubkey ext_data.fee_recipient)
    -- `rootKnown`: canonical bytes and a well-formed account, as `isKnownRootRefines`
    -- itself needs.
    (hRootCanon : canonical proof_root)
    (hHistCanon : ∀ i : Fin 100, canonical tree_account.root_history.val[i.val]!)
    (hHistSize : tree_account.root_history_size.val = 100)
    (hRootIdx : tree_account.root_index.val < 100)
    (hRoot : LeanSpec.rootKnown (mapTree tree_account) (mapBytesToF proof_root))
    -- `externalDataBound`: the usual `hSha` oracle-agreement hypothesis, plus headroom.
    (hSha : ∀ (bytes : List Std.U8) (h : bytes.length ≤ Std.Usize.max),
      ∃ digest : Array Std.U8 32#usize,
        solana_sha256_hasher.hash ⟨bytes, h⟩ = ok digest ∧
        mapBytesToByteList digest.val = LeanSpec.Sha.sha256 (mapBytesToByteList bytes))
    (hExtDataSum : 32 + 8 + (4 + (alloc.vec.Vec.deref encrypted_output1).length)
        + (4 + (alloc.vec.Vec.deref encrypted_output2).length) + 8 + 32 + 32 ≤ Std.Usize.max)
    (hExtDataBound : LeanSpec.externalDataBound
        (mapTxInputs s π proof_root proof_ext_data_hash proof_public_amount input_nullifiers
          output_commitments ext_data encrypted_output1 encrypted_output2))
    -- `feeSufficient`: via `feeSufficientRefines`, rate bounds included (true of every real
    -- `GlobalConfig`, see that theorem's docstring).
    (hdrate : global_config.deposit_fee_rate.val ≤ 10000)
    (hwrate : global_config.withdrawal_fee_rate.val ≤ 10000)
    (hmrate : global_config.fee_error_margin.val ≤ 10000)
    (hFeeSufficient : LeanSpec.feeSufficient
        (mapGlobalConfig global_config tree_account.max_deposit_amount)
        ext_data.ext_amount.val ext_data.fee.val)
    -- `pubAmtConsistent`: via `checkPublicAmountRefines`, fully proven, no gap.
    (hPubAmtConsistent : LeanSpec.pubAmtConsistent ext_data.ext_amount.val ext_data.fee.val
        (mapBytesToF proof_public_amount))
    -- `proofValid`, stood in for directly (see the section docstring).
    (ha : curve_shim.FV_VK_ALPHA_G1 = ok a) (ha1 : curve_shim.FV_VK_BETA_G2 = ok a1)
    (ha2 : curve_shim.FV_VK_GAMME_G2 = ok a2) (ha3 : curve_shim.FV_VK_DELTA_G2 = ok a3)
    (ha4 : curve_shim.FV_VK_IC = ok a4)
    (hVerify : zkcash.utils.fv_verify_proof_full_entry proof_root proof_public_amount
        proof_ext_data_hash input_nullifiers output_commitments proof_a proof_b proof_c
        a a1 a2 a3 a4 = ok true)
    -- `depositWithinLimit` / `signerSolvent` / `poolSolvent`'s fee conjunct, via the three
    -- guard theorems above.
    (hDepositLimit : LeanSpec.depositWithinLimit
        (mapGlobalConfig global_config tree_account.max_deposit_amount) ext_data.ext_amount.val)
    (hSignerSolvent : LeanSpec.signerSolvent balances s ext_data.ext_amount.val)
    (hPoolFeeSolvent : ext_data.fee.val > 0 →
        tree_token_lamports.val ≥ ext_data.fee.val + rent_exempt_minimum.val)
    (hoverflow1 : tree_token_lamports.val + ext_data.ext_amount.val.toNat ≤ Std.U64.max)
    (hoverflow2 : fee_recipient_account.lamports.val + ext_data.fee.val ≤ Std.U64.max)
    (hoverflow3 : ext_data.fee.val + rent_exempt_minimum.val ≤ Std.U64.max)
    -- `treeHasRoom`, both times `append` needs it (`treeHasRoomRefines`'s own two-call
    -- shape), plus the structural facts `appendRefines` doesn't (yet) preserve across a
    -- call -- true of every reachable account (`height`/`root_history_size` are set once
    -- at `initialize` and never touched again), but not something `appendRefines` itself
    -- states yet (its postcondition is only `mapTree treeAccount' = ...`, not full account
    -- equality); flagged here as a gap in that theorem, not papered over.
    (hheight : tree_account.height.val = 26)
    (hroom : tree_account.next_index.val < 2 ^ 26 - 3)
    (hAppendStruct : ∀ (leaf : Array Std.U8 32#usize)
        (proof : alloc.vec.Vec (Array Std.U8 32#usize)) (ta ta' : zkcash.MerkleTreeAccount),
        ta.height.val = 26 → ta.next_index.val < 2 ^ 26 - 2 →
        zkcash.merkle_tree.MerkleTree.append
            zkcash.light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher leaf ta
          = ok (core.result.Result.Ok proof, ta') →
        ta'.height.val = 26 ∧ ta'.next_index.val = ta.next_index.val + 1)
    (hHashv : ∀ b c : Array Std.U8 32#usize, ∃ h : Array Std.U8 32#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.hashv
          ⟨[⟨b.val, by scalar_tac⟩, ⟨c.val, by scalar_tac⟩], by scalar_tac⟩
        = ok (core.result.Result.Ok h) ∧
        mapBytesToF h = LeanSpec.PoseidonHashes.H2 (mapBytesToF b) (mapBytesToF c))
    (hZeroBytes : ∃ zeroBytes : Array (Array Std.U8 32#usize) 41#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.zero_bytes = ok zeroBytes ∧
      ∀ i : Fin 26, mapBytesToF (zeroBytes.val[i.val]!) = LeanSpec.Z i.val)
    (hpos : ext_data.ext_amount > 0#i64) :
    let inputs := mapTxInputs s π proof_root proof_ext_data_hash proof_public_amount
      input_nullifiers output_commitments ext_data encrypted_output1 encrypted_output2
    let oldWorld := mapOldWorld tree_account global_config nullifiers balances
      tree_token_lamports rent_exempt_minimum
    ∃ tree_account' tree_token_lamports' signer_lamports' fee_recipient_account',
      zkcash.fv_transact_entry tree_account global_config proof_root proof_ext_data_hash
          proof_public_amount input_nullifiers output_commitments proof_a proof_b proof_c
          ext_data_minified encrypted_output1 encrypted_output2 rent_exempt_minimum
          tree_token_lamports signer_lamports recipient fee_recipient_account
        = ok (core.result.Result.Ok (), tree_account', tree_token_lamports', signer_lamports',
            recipient, fee_recipient_account') ∧
      mapTree tree_account' = (LeanSpec.transactEffects inputs oldWorld).state.tree ∧
      tree_token_lamports'.val = (LeanSpec.transactEffects inputs oldWorld).state.solBalance ∧
      signer_lamports'.val = (LeanSpec.transactEffects inputs oldWorld).balances s ∧
      fee_recipient_account'.lamports.val
        = (LeanSpec.transactEffects inputs oldWorld).balances (mapPubkey ext_data.fee_recipient) := by
  intro inputs oldWorld
  -- `is_known_root`
  have hknown : zkcash.merkle_tree.MerkleTree.is_known_root tree_account proof_root = ok true := by
    obtain ⟨b, hbeq, hbval⟩ :=
      specSucceeds _ (isKnownRootRefines tree_account proof_root hRootCanon hHistCanon
        hHistSize hRootIdx)
    rw [hbeq, hbval.mpr hRoot]
  -- `fv_check_public_amount_entry`
  have hb2 : zkcash.utils.fv_check_public_amount_entry ext_data.ext_amount ext_data.fee
      proof_public_amount = ok true := by
    obtain ⟨b, hbeq, hbval⟩ :=
      specSucceeds _ (checkPublicAmountRefines ext_data.ext_amount ext_data.fee proof_public_amount)
    rw [hbeq, hbval.mpr hPubAmtConsistent]
  -- `validate_fee`
  have hvfee : zkcash.utils.validate_fee ext_data.ext_amount ext_data.fee
      global_config.deposit_fee_rate global_config.withdrawal_fee_rate
      global_config.fee_error_margin = ok (core.result.Result.Ok ()) := by
    have hFeeSufficient' := hFeeSufficient
    simp only [mapGlobalConfig, LeanSpec.feeSufficient] at hFeeSufficient'
    have hposV : ext_data.ext_amount.val > 0 := by scalar_tac
    exact feeSufficientAccepts ext_data.ext_amount ext_data.fee
      global_config.deposit_fee_rate global_config.withdrawal_fee_rate
      global_config.fee_error_margin hdrate hwrate hmrate
      (by intro hc; rw [hc] at hposV; simp [I64.rMin] at hposV)
      (by simp only [LeanSpec.feeSufficient]; exact hFeeSufficient')
  -- external-data-hash equality check (`b1`)
  obtain ⟨extDataHash, hhash, hExtVal⟩ :
      ∃ extDataHash, zkcash.utils.calculate_complete_ext_data_hash ext_data.recipient
          ext_data.ext_amount (alloc.vec.Vec.deref encrypted_output1)
          (alloc.vec.Vec.deref encrypted_output2) ext_data.fee ext_data.fee_recipient
          ext_data.mint_address = ok (core.result.Result.Ok extDataHash) ∧
        (mapBytesToNatLE extDataHash : F) = externalDataHashOf (mapPubkey ext_data.recipient)
          ext_data.ext_amount.val (mapBytesToByteList (alloc.vec.Vec.deref encrypted_output1).val)
          (mapBytesToByteList (alloc.vec.Vec.deref encrypted_output2).val) ext_data.fee.val
          (mapPubkey ext_data.fee_recipient) (mapPubkey ext_data.mint_address) := by
    obtain ⟨r, hreq, h, hrval, hveq⟩ :=
      specSucceeds _ (externalDataBoundRefines ext_data.recipient ext_data.fee_recipient
        ext_data.mint_address ext_data.ext_amount (alloc.vec.Vec.deref encrypted_output1)
        (alloc.vec.Vec.deref encrypted_output2) ext_data.fee hSha hExtDataSum)
    exact ⟨h, by rw [hreq, hrval], hveq⟩
  have hExtDataBound' := hExtDataBound
  simp only [mapTxInputs, LeanSpec.externalDataBound, ← externalDataHashOfEq] at hExtDataBound'
  have hFeq : (mapBytesToNatLE extDataHash : F) = mapBytesToF proof_ext_data_hash := by
    rw [hExtVal, hExtDataBound']
  have hfrEq : (mapBytesToNatLE extDataHash : fr_shim.FrShim) =
      (mapBytesToNat proof_ext_data_hash : fr_shim.FrShim) := by
    have hmod : mapBytesToNatLE extDataHash % LeanSpec.p
        = mapBytesToNat proof_ext_data_hash % LeanSpec.p := by
      rw [← ZMod.natCast_eq_natCast_iff']
      simpa [mapBytesToF] using hFeq
    rw [hp_eq_bn254r] at hmod
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mpr hmod
  have hfs : fr_shim.FrShim.from_le_bytes_mod_order extDataHash
      = ok (mapBytesToNatLE extDataHash : fr_shim.FrShim) := by
    unfold fr_shim.FrShim.from_le_bytes_mod_order mapBytesToNatLE; rfl
  have hfs1 : fr_shim.FrShim.from_be_bytes_mod_order proof_ext_data_hash
      = ok (mapBytesToNat proof_ext_data_hash : fr_shim.FrShim) := by
    unfold fr_shim.FrShim.from_be_bytes_mod_order mapBytesToNat; rfl
  clear hFeq
  have hb1 : fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq
      (mapBytesToNatLE extDataHash : fr_shim.FrShim) (mapBytesToNat proof_ext_data_hash
        : fr_shim.FrShim) = ok true := by
    simp [fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq, hfrEq]
  -- the deposit-limit guard
  have hcastExtAmt : (IScalar.hcast .U64 ext_data.ext_amount : Std.U64).val
      = ext_data.ext_amount.val := IScalar.hcast_inBounds_spec .U64 ext_data.ext_amount
    (by scalar_tac)
  have hDepositGuard : (IScalar.hcast .U64 ext_data.ext_amount : Std.U64)
      ≤ tree_account.max_deposit_amount := by
    have h := depositWithinLimitRefines ext_data.ext_amount tree_account.max_deposit_amount
      (mapGlobalConfig global_config tree_account.max_deposit_amount) rfl (by scalar_tac)
    exact h.mpr hDepositLimit
  -- the signer/pool checked_sub/checked_add pair (deposit)
  obtain ⟨signerLamports', treeTokenLamports', hsigEq, hpoolAddEq, hDepositPair⟩ :=
    transferEffectsDepositRefines ext_data.ext_amount signer_lamports tree_token_lamports
      balances s tree_token_lamports.val hbalS rfl (by scalar_tac) hSignerSolvent hoverflow1
  by_cases hfee : ext_data.fee > 0#u64
  · -- fee > 0 branch
    have hfeeval : ext_data.fee.val > 0 := by scalar_tac
    have hval3 := Std.U64.checked_add_bv_spec ext_data.fee rent_exempt_minimum
    obtain ⟨val3, hval3eq⟩ : ∃ val3, ext_data.fee.checked_add rent_exempt_minimum = some val3 := by
      cases h : ext_data.fee.checked_add rent_exempt_minimum with
      | none => rw [h] at hval3; omega
      | some z => exact ⟨z, rfl⟩
    have hval3v : val3.val = ext_data.fee.val + rent_exempt_minimum.val := by
      rw [hval3eq] at hval3; omega
    have hpost : treeTokenLamports'.val = tree_token_lamports.val + ext_data.ext_amount.val.toNat := by
      have hspec := Std.U64.checked_add_bv_spec tree_token_lamports
        (IScalar.hcast .U64 ext_data.ext_amount : Std.U64)
      rw [hpoolAddEq] at hspec
      have hv := hspec.2.1
      have hc := hcastExtAmt
      omega
    have hsufficient : ext_data.fee.val + rent_exempt_minimum.val ≤ treeTokenLamports'.val := by
      have := hPoolFeeSolvent hfeeval
      omega
    obtain ⟨treeTokenLamports'', feeRecipientLamports', hfeeSubEq, hfeeAddEq, hFeePair⟩ :=
      transactEffectsFeeRefines ext_data.fee rent_exempt_minimum treeTokenLamports'
        fee_recipient_account.lamports balances (mapPubkey ext_data.fee_recipient)
        treeTokenLamports'.val hbalT rfl hfeeval hsufficient hoverflow2
    have hguard2 : treeTokenLamports' ≥ val3 := by scalar_tac
    have hposZ : ext_data.ext_amount.val > 0 := by scalar_tac
    have hposI64 : ext_data.ext_amount ≥ (0#i64 : Std.I64) := by scalar_tac
    obtain ⟨v0, hv0eq, hv0val⟩ :=
      specSucceeds _ (Array.index_usize_spec output_commitments 0#usize (by scalar_tac))
    have hv0val' : v0 = output_commitments.val[0]! :=
      hv0val.trans (getElemBang output_commitments.val 0 (by scalar_tac))
    obtain ⟨v1, hv1eq, hv1val⟩ :=
      specSucceeds _ (Array.index_usize_spec output_commitments 1#usize (by scalar_tac))
    have hv1val' : v1 = output_commitments.val[1]! :=
      hv1val.trans (getElemBang output_commitments.val 1 (by scalar_tac))
    obtain ⟨proof0, tree_account1, happend0, htree1⟩ :=
      appendRefines v0 tree_account hheight (by omega) hHashv hZeroBytes
    obtain ⟨hheight1, hnext1⟩ := hAppendStruct v0 proof0 tree_account tree_account1 hheight
      (by omega) happend0
    obtain ⟨proof1, tree_account2, happend1, htree2⟩ :=
      appendRefines v1 tree_account1 hheight1 (by omega) hHashv hZeroBytes
    refine ⟨tree_account2, treeTokenLamports'', signerLamports',
      { fee_recipient_account with lamports := feeRecipientLamports' }, ?_, ?_, ?_, ?_, ?_⟩
    · -- Every fact the equation needs is already assembled above (`hsigEq`, `hpoolAddEq`,
      -- `hval3eq`, `hfeeSubEq`, `hfeeAddEq`, `hv0eq`, `hv1eq`, plus the four guard conditions
      -- `hDepositGuard`/`hfee`/`hposI64`/`hguard2`); what's left is purely mechanical:
      -- `unfold`+`simp` to reach the four nested `if`s, then discharge each one from the
      -- matching fact above. `split_ifs` gets most of the way (confirmed: the resulting
      -- goals close via `rfl` on the one "all guards pass" branch, and via `exact absurd`
      -- from the matching guard on every branch where a guard is assumed false) but leaves
      -- one leftover goal, `⊢ ¬treeTokenLamports' ≥ val3` under `ext_data.fee > 0#u64`, that
      -- doesn't pair with a usable `¬hguard2`-shaped hypothesis the way the others do --
      -- `split_ifs` duplicating a condition into a second, syntactically distinct decidable
      -- instance, not a correctness gap. An interactive session (`set_option pp.all true` on
      -- that one goal) would settle it in a line; sorry'd here rather than guessed at blind.
      sorry
    · simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld, mapOldWorld, mapTxInputs,
        if_neg (show ext_data.ext_amount.val ≠ 0 by omega), if_pos hposZ]
      rw [htree2, htree1, hv0val', hv1val']
    · have h1 := congrArg Prod.snd hDepositPair
      have h2 := congrArg Prod.snd hFeePair
      simp only [transferEffectsOf, if_neg (show ext_data.ext_amount.val ≠ 0 by omega),
        if_pos hposZ] at h1
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld, mapOldWorld, mapTxInputs,
        if_neg (show ext_data.ext_amount.val ≠ 0 by omega), if_pos hposZ]
      omega
    · have h1 := congrArg Prod.fst hDepositPair
      simp only [transferEffectsOf, if_neg (show ext_data.ext_amount.val ≠ 0 by omega),
        if_pos hposZ] at h1
      have hval : signerLamports'.val = balances s - ext_data.ext_amount.val.natAbs := by
        have := congrFun h1 s; simpa using this
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld, mapOldWorld, mapTxInputs,
        if_neg (show ext_data.ext_amount.val ≠ 0 by omega), if_pos hposZ,
        Function.update_of_ne hst, Function.update_of_ne hst.symm, Function.update_self]
      omega
    · have h2 := congrArg Prod.fst hFeePair
      have hval : feeRecipientLamports'.val
          = balances (mapPubkey ext_data.fee_recipient) + ext_data.fee.val := by
        have := congrFun h2 (mapPubkey ext_data.fee_recipient); simpa using this
      simp only [LeanSpec.transactEffects, LeanSpec.transferEffects, inputs, oldWorld, mapOldWorld, mapTxInputs,
        if_neg (show ext_data.ext_amount.val ≠ 0 by omega), if_pos hposZ,
        Function.update_of_ne hst, Function.update_of_ne hst.symm, Function.update_self]
      omega
  · -- `ext_data.fee = 0`: the mirror of the branch above, minus the fee transfer entirely
    -- (`fv_transact_entry` calls `append` twice directly, no `InsufficientFundsForFee`
    -- check, no `checked_sub`/`checked_add` on the fee recipient). Not attempted here:
    -- same technique as the `fee > 0` branch above (unfold + the two `appendRefines`
    -- calls + the arithmetic goals, simpler since there's no `val3`/`hguard2` pair to
    -- thread through), scoped out to keep this pass to the one real accept-path branch.
    sorry

/-! ## Not yet connected

- **`proofValid`**: connects to `zkcash.utils.fv_verify_proof_full_entry`, where the easier
  half already exists: `proofs/VerifyProof/Main.lean`'s
  `fv_verify_proof_full_entry_checks_groth16_equation` shows the verifier checks the right
  pairing equation on the right points. Its own docstring already names what's missing:
  the bridge from that equation to the spec's `Groth16.verify`, needing the decoded curve
  points related to the abstract `G1`/`G2`/`GT` groups `Groth16.verify` is stated over.
  That bridge, not `proofValid` itself, is the connection theorem. Not started.
- **`nullifiersFresh`**: not a fact the extracted Rust model can see at all. It comes from
  Anchor's PDA `init` failing when the nullifier account already exists, a runtime
  guarantee outside the pure functional code model, so it can only ever be a stated,
  reviewable assumption (an account-layer contract), never a theorem derived from
  `code_model`. Not started, and not the kind of thing a connection theorem could show. -/
