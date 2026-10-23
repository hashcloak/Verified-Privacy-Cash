import Connection.Proofs.HandlerComplete
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # A toy deployment (not for review)

A deliberately broken toy, used only to show that hypotheses can hold together (non-vacuity)
and to build counterexamples: `G1 = G2 = GT = Unit`, every pairing is 1, Poseidon always
returns 1, SHA-256 always returns 32 zero bytes. The G1 decoding is the real one
(`syscallDecodeG1`); the syscalls answer exactly when their G1 points decode. -/

namespace Connection.Toy
open zkcash_core

def zeros32 : Std.Array U8 32#usize := Std.Array.repeat 32#usize 0#u8
def one32 : Std.Array U8 32#usize := Std.Array.make 32#usize (List.replicate 31 0#u8 ++ [1#u8]) (by simp)
def zeros64 : Std.Array U8 64#usize := Std.Array.repeat 64#usize 0#u8

theorem beNat_zeros32 : beNat zeros32 = 0 := by rfl
theorem beNat_one32 : beNat one32 = 1 := by rfl
theorem toF_zeros32 : toF zeros32 = 0 := by simp only [toF, beNat_zeros32, Nat.cast_zero]
theorem toF_one32 : toF one32 = 1 := by simp only [toF, beNat_one32, Nat.cast_one]
theorem canonical_zeros32 : Canonical zeros32 := by
  simp only [Canonical, beNat_zeros32]; decide
theorem canonical_one32 : Canonical one32 := by
  simp only [Canonical, beNat_one32]; decide

theorem decode_zeros64 : syscallDecodeG1 zeros64 = some ⟨0, 0, true⟩ := by
  simp [syscallDecodeG1, zeros64, Std.Array.repeat_val]

/-! ## The syscalls -/

/-- The four G1 points of a pairing input decode. -/
def pairingG1Decode (input : Std.Array U8 768#usize) : Bool :=
  (syscallDecodeG1 (bytesAt input 0 64#usize (by simp))).isSome &&
  (syscallDecodeG1 (bytesAt input 192 64#usize (by simp))).isSome &&
  (syscallDecodeG1 (bytesAt input 384 64#usize (by simp))).isSome &&
  (syscallDecodeG1 (bytesAt input 576 64#usize (by simp))).isSome

/-- Toy syscalls: they answer (with the identity, or 1) exactly when their G1 points decode. -/
def toyAltBn : AltBn128 where
  multiplication input :=
    if (syscallDecodeG1 (bytesAt input 0 64#usize (by simp))).isSome then some zeros64 else none
  addition input :=
    if (syscallDecodeG1 (bytesAt input 0 64#usize (by simp))).isSome &&
       (syscallDecodeG1 (bytesAt input 64 64#usize (by simp))).isSome then some zeros64 else none
  pairing input := if pairingG1Decode input then some one32 else none

theorem isSome_map {α β : Type} {o : Option α} (f : α → β) (h : o.isSome = true) :
    o.map f = some (f (o.get h)) := by
  cases o with
  | none => simp at h
  | some x => rfl

def toyC : @AltBn128Contracts toyAltBn Unit Unit Unit _ (@CommGroup.toCommMonoid Unit _) where
  e := fun _ _ => 1
  embed := fun _ => ()
  embed_neg := fun _ => rfl
  decodeG1 b := (syscallDecodeG1 b).map (fun _ => ())
  decodeG1_eq := fun _ => rfl
  decodeG2 := fun _ => some ()
  mul := by
    intro input out h
    simp only [toyAltBn] at h
    split at h
    · rename_i hd
      obtain rfl := (Option.some.inj h)
      exact ⟨(), isSome_map _ hd, by rw [decode_zeros64]; rfl⟩
    · cases h
  add := by
    intro input out h
    simp only [toyAltBn] at h
    split at h
    · rename_i hd
      simp only [Bool.and_eq_true] at hd
      obtain rfl := (Option.some.inj h)
      exact ⟨(), (), isSome_map _ hd.1, isSome_map _ hd.2, by rw [decode_zeros64]; rfl⟩
    · cases h
  pairing := by
    intro input out h _
    simp only [toyAltBn] at h
    split at h
    · rename_i hd
      simp only [pairingG1Decode, Bool.and_eq_true] at hd
      exact ⟨(), (), (), (), (), (), (), (), isSome_map _ hd.1.1.1, rfl, isSome_map _ hd.1.1.2, rfl,
        isSome_map _ hd.1.2, rfl, isSome_map _ hd.2, rfl, rfl⟩
    · cases h

theorem toySyscalls : SyscallsSucceed toyC where
  mul := by
    intro input h
    refine ⟨zeros64, ?_⟩
    simp only [toyAltBn]
    rw [if_pos]
    cases hd : syscallDecodeG1 (bytesAt input 0 64#usize (by simp)) with
    | none => exact absurd (by simp [toyC, hd]) h
    | some _ => rfl
  add := by
    intro input h1 h2
    refine ⟨zeros64, ?_⟩
    simp only [toyAltBn]
    rw [if_pos]
    simp only [Bool.and_eq_true]
    constructor
    · cases hd : syscallDecodeG1 (bytesAt input 0 64#usize (by simp)) with
      | none => exact absurd (by simp [toyC, hd]) h1
      | some _ => rfl
    · cases hd : syscallDecodeG1 (bytesAt input 64 64#usize (by simp)) with
      | none => exact absurd (by simp [toyC, hd]) h2
      | some _ => rfl
  pairing := by
    intro input P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ d1 _ d2 _ d3 _ d4 _
    refine ⟨one32, ?_, ?_⟩
    · simp only [toyAltBn]
      rw [if_pos]
      simp only [pairingG1Decode, Bool.and_eq_true]
      simp only [toyC, Option.map_eq_some_iff] at d1 d2 d3 d4
      obtain ⟨_, h1, -⟩ := d1; obtain ⟨_, h2, -⟩ := d2
      obtain ⟨_, h3, -⟩ := d3; obtain ⟨_, h4, -⟩ := d4
      simp [h1, h2, h3, h4]
    · exact ⟨fun _ => rfl, fun _ => by decide⟩

theorem toyLaws : PairingLaws toyC.e :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

theorem toyKey : KeyG2Decodes toyC := ⟨by simp [toyC], by simp [toyC], by simp [toyC]⟩

/-! ## The hashes -/

/-- The zero hashes: `0`, then `1` (Poseidon always returns 1). -/
def toyZ : Std.Array (Std.Array U8 32#usize) 41#usize :=
  Std.Array.make 41#usize (zeros32 :: List.replicate 40 one32) (by simp)

def toyHasher : merkle_tree.Hasher Unit := ⟨fun _ _ => ok one32, ok toyZ⟩
def toySha256 : ext_data.Sha256 Unit := ⟨fun _ => ok zeros32⟩
@[reducible] def toyCrypto : Crypto := ⟨toyHasher, toySha256, toyAltBn⟩

/-- Spec instances matching the toy hashes: `H2` is constant 1, `sha256` returns 32 zero bytes.
    The code never computes `H1`, `H3`, `H4` (only the circuit does); they are chosen so that
    the toy run's transactions have circuit witnesses (`Proofs/ToyRun.lean`): `H1` is the
    identity, `H3` and `H4` add their arguments. -/
@[reducible] def toyPoseidon : LeanSpec.PoseidonHashes :=
  ⟨fun a => a, fun _ _ => 1, fun a b c => a + b + c, fun a b c d => a + b + c + d⟩
@[reducible] def toySpecSha : LeanSpec.Sha := ⟨fun _ => List.replicate 32 0⟩

attribute [local instance] toyPoseidon toySpecSha

theorem toyZ_zero : toyZ.val[0]! = zeros32 := by rfl
theorem toyZ_succ (i : ℕ) (hi : i < 40) : toyZ.val[i + 1]! = one32 := by
  show (zeros32 :: List.replicate 40 one32)[i + 1]! = one32
  rw [getElem!_pos _ _ (by simp only [List.length_cons, List.length_replicate]; omega),
    List.getElem_cons_succ, List.getElem_replicate]

theorem toyZ_canonical (i : ℕ) (hi : i ≤ 26) : Canonical (toyZ.val[i]!) := by
  cases i with
  | zero => rw [toyZ_zero]; exact canonical_zeros32
  | succ i => rw [toyZ_succ i (by omega)]; exact canonical_one32

theorem spec_Z (i : ℕ) : LeanSpec.Z i = if i = 0 then 0 else 1 := by
  cases i <;> rfl

theorem toyHashesAgree : HashesAgree toyCrypto where
  poseidon := by
    intro a b h hh
    obtain rfl := (Result.ok_injective hh).symm
    rw [toF_one32]; rfl
  zeroBytes := ⟨toyZ, rfl, fun i hi => by
    rw [spec_Z]
    cases i with
    | zero => rw [toyZ_zero, toF_zeros32]; rfl
    | succ i => rw [toyZ_succ i (by omega), toF_one32]; rfl⟩
  sha256 := by
    intro x h hh
    obtain rfl := (Result.ok_injective hh).symm
    rfl
  poseidonCanonical := by
    intro a b h hh
    obtain rfl := (Result.ok_injective hh).symm
    exact canonical_one32
  zeroBytesCanonical := ⟨toyZ, rfl, toyZ_canonical⟩

theorem toyHashesSucceed : HashesSucceed toyCrypto :=
  ⟨fun _ _ _ _ => ⟨one32, rfl⟩, fun _ => ⟨zeros32, rfl⟩⟩

/-! ## A toy transaction, for the handler -/

def pk (n : U8) : Pubkey := Std.Array.make 32#usize (n :: List.replicate 31 0#u8) (by simp)

def toyAccounts : TransactAccounts :=
  { treeAccount := pk 5#u8, nullifier0 := pk 6#u8, nullifier1 := pk 7#u8, nullifier2 := pk 8#u8,
    nullifier3 := pk 9#u8, treeTokenAccount := pk 2#u8, globalConfig := pk 10#u8,
    recipient := pk 3#u8, feeRecipientAccount := pk 4#u8, signer := pk 1#u8,
    systemProgram := systemProgram }

/-- Every account holds `bal` lamports, owned by the system program, no data. -/
def toyState (bal : U64) : State := fun _ => { Account.default with lamports := bal }

def toyTree : merkle_tree.MerkleTreeAccount :=
  { authority := zeros32, next_index := 0#u64, subtrees := Std.Array.repeat 26#usize zeros32,
    root := one32, root_history := Std.Array.repeat 100#usize one32, root_index := 0#u64,
    max_deposit_amount := 1#u64, height := 26#u8, root_history_size := 100#u8, bump := 0#u8,
    _padding := Std.Array.repeat 5#usize 0#u8 }

def toyConfig : admin.GlobalConfig := ⟨zeros32, 0#u16, 0#u16, 0#u16, 0#u8⟩

def toyProof (pa : Std.Array U8 64#usize) (pubAmt : Std.Array U8 32#usize) : transact.Proof :=
  { proof_a := pa, proof_b := Std.Array.repeat 128#usize 0#u8, proof_c := zeros64,
    root := one32, public_amount := pubAmt, ext_data_hash := zeros32,
    input_nullifiers := Std.Array.make 2#usize [zeros32, one32] (by simp),
    output_commitments := Std.Array.make 2#usize [zeros32, zeros32] (by simp) }

def emptySlice : Slice U8 := Slice.from [] (by simp)

theorem toyTree_shape : TreeShape toyTree := by simp [TreeShape, toyTree]

theorem toyTree_hist : ∀ j : Fin 100, Canonical toyTree.root_history.val[j.val]! := by
  intro j
  have : toyTree.root_history.val[j.val]! = one32 := by
    rw [getElem!_pos _ _ (by simp)]; simp only [toyTree, Std.Array.repeat_val, List.getElem_replicate]
  rw [this]; exact canonical_one32

theorem toyTree_sub : ∀ j : Fin 26, Canonical toyTree.subtrees.val[j.val]! := by
  intro j
  have : toyTree.subtrees.val[j.val]! = zeros32 := by
    rw [getElem!_pos _ _ (by simp)]; simp only [toyTree, Std.Array.repeat_val, List.getElem_replicate]
  rw [this]; exact canonical_zeros32

theorem pk_ne {m n : U8} (h : m ≠ n) : pk m ≠ pk n := by
  intro e
  have := congrArg (fun a : Pubkey => a.val[0]!) e
  simp [pk, Std.Array.make] at this
  exact h this

theorem toyFit : emptySlice.length + emptySlice.length + 120 ≤ Usize.max := by
  simp [emptySlice, Slice.length]; scalar_tac

/-! ## Counterexamples to the faithful handler-completeness statement -/

theorem toy_alpha_decodes : toyC.decodeG1 verifying_key.VERIFYING_KEY.vk_alpha_g1 = some () := by
  have h : (syscallDecodeG1 verifying_key.VERIFYING_KEY.vk_alpha_g1).isSome = true := key_alpha_decodes
  show (syscallDecodeG1 _).map _ = _
  rw [isSome_map _ h]

theorem toy_zeros_decodes : toyC.decodeG1 zeros64 = some () := by
  simp only [toyC, decode_zeros64]; rfl

/-- The spec's preconditions for the handler's view, with the groups' instances as parameters. -/
def HandlerPre (G1 G2 GT : Type) [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
    [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (a : TransactAccounts) (s₁ : State) (v : U64) (tree : merkle_tree.MerkleTreeAccount)
    (config : admin.GlobalConfig) (spent : Finset LeanSpec.F) (proof : transact.Proof)
    (ext : I64) (fee : U64) (out1 out2 : Slice U8) : Prop :=
  @LeanSpec.transactPreconditions _ (syscallGroups C) (inferInstanceAs (AddCommGroup G1))
    (inferInstanceAs (Module LeanSpec.F G1)) (inferInstanceAs (AddCommGroup G2))
    (inferInstanceAs (Module LeanSpec.F G2)) (inferInstanceAs (CommGroup GT))
    (syscallPairing C laws) (@LeanSpec.Deployment.mk (syscallGroups C) (programKey C)) (toInputs a proof ext fee out1 out2)
    (handlerWorld a s₁ v tree config spent)

theorem toy_pre_L1 : HandlerPre Unit Unit Unit toyCrypto toyC toyLaws toyAccounts (toyState 0#u64)
    0#u64 toyTree toyConfig ∅ (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32) 0#i64 0#u64
    emptySlice emptySlice := by
  unfold HandlerPre
  have hdec := decode_toInputs toyC (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32)
    toyAccounts 0#i64 0#u64 emptySlice emptySlice toy_alpha_decodes rfl toy_zeros_decodes
  have hk0 : (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32).input_nullifiers.val[0]! = zeros32 := rfl
  have hk1 : (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32).input_nullifiers.val[1]! = one32 := rfl
  have h10 : (1 : LeanSpec.F) ≠ 0 := by decide
  have he : (toInputs toyAccounts (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32) 0#i64 0#u64
      emptySlice emptySlice).extAmt = 0 := by simp [toInputs]
  have hf : (toInputs toyAccounts (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32) 0#i64 0#u64
      emptySlice emptySlice).f = 0 := by simp [toInputs]
  refine @LeanSpec.transactPreconditions.mk _ (syscallGroups toyC) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit)) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit)) (inferInstanceAs (CommGroup Unit))
    (syscallPairing toyC toyLaws) (@LeanSpec.Deployment.mk (syscallGroups toyC) (programKey toyC)) _ _
    ?_ ?_ ?_ ?_ ⟨_, hdec, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show LeanSpec.rootBytesKnown (toTree toyTree) (toBytes one32.val)
    rw [rootBytesKnown_iff]
    refine ⟨canonical_one32, ⟨⟨0, ?_⟩, by rw [toF_one32]; exact h10⟩⟩
    show toF (toyTree.root_history.val[0]!) = toF one32
    rfl
  · show (LeanSpec.natOfLE (List.replicate 32 0) : LeanSpec.F) = toF zeros32
    rw [toF_zeros32]; rfl
  · unfold LeanSpec.feeSufficient; rw [he, hf]; simp
  · unfold LeanSpec.pubAmtConsistent; rw [he, hf]
    refine ⟨fun h => by omega, ?_⟩
    show toF zeros32 = _; rw [toF_zeros32]; simp
  · simp [LeanSpec.nullifiersFresh, handlerWorld]
  · show toF _ ≠ toF _
    rw [hk0, hk1, toF_zeros32, toF_one32]; exact h10.symm
  · intro h; rw [he] at h; omega
  · unfold LeanSpec.poolSolvent; rw [he, hf]
    exact ⟨fun h => by omega, fun h => by omega⟩
  · unfold LeanSpec.signerSolvent; rw [he]; simp [handlerWorld]
  · show toyTree.next_index.val ≤ 2 ^ 26 - 2; simp [toyTree]
  · unfold LeanSpec.amountsInRange; rw [he, hf]; norm_num
  · simp [LeanSpec.encOutsFit, toInputs, emptySlice, toBytes]
  · refine ⟨fun e => pk_ne (by decide : (1#u8 : U8) ≠ 2#u8) (toPubkey_inj e), fun h => ?_, fun h => ?_⟩
    · rw [he] at h; omega
    · rw [hf] at h; omega
  · intro i
    show LeanSpec.canonicalEncoding (toBytes ((publicInputs _)[i.val]!).val) _
    rw [canonicalEncoding_iff]
    fin_cases i
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
  · refine ⟨fun k hk => ?_, fun h => by rw [he] at h; omega⟩
    exfalso
    unfold LeanSpec.balanceDelta at hk
    rw [he, hf] at hk
    simp at hk
theorem toy_pre_A0 : HandlerPre Unit Unit Unit toyCrypto toyC toyLaws toyAccounts (toyState 1#u64)
    0#u64 toyTree toyConfig ∅ (toyProof zeros64 one32) 1#i64 0#u64
    emptySlice emptySlice := by
  unfold HandlerPre
  have hdec := decode_toInputs toyC (toyProof zeros64 one32)
    toyAccounts 1#i64 0#u64 emptySlice emptySlice toy_zeros_decodes rfl toy_zeros_decodes
  have hk0 : (toyProof zeros64 one32).input_nullifiers.val[0]! = zeros32 := rfl
  have hk1 : (toyProof zeros64 one32).input_nullifiers.val[1]! = one32 := rfl
  have h10 : (1 : LeanSpec.F) ≠ 0 := by decide
  have he : (toInputs toyAccounts (toyProof zeros64 one32) 1#i64 0#u64
      emptySlice emptySlice).extAmt = 1 := by simp [toInputs]
  have hf : (toInputs toyAccounts (toyProof zeros64 one32) 1#i64 0#u64
      emptySlice emptySlice).f = 0 := by simp [toInputs]
  refine @LeanSpec.transactPreconditions.mk _ (syscallGroups toyC) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit)) (inferInstanceAs (AddCommGroup Unit))
    (inferInstanceAs (Module LeanSpec.F Unit)) (inferInstanceAs (CommGroup Unit))
    (syscallPairing toyC toyLaws) (@LeanSpec.Deployment.mk (syscallGroups toyC) (programKey toyC)) _ _
    ?_ ?_ ?_ ?_ ⟨_, hdec, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · show LeanSpec.rootBytesKnown (toTree toyTree) (toBytes one32.val)
    rw [rootBytesKnown_iff]
    refine ⟨canonical_one32, ⟨⟨0, ?_⟩, by rw [toF_one32]; exact h10⟩⟩
    show toF (toyTree.root_history.val[0]!) = toF one32
    rfl
  · show (LeanSpec.natOfLE (List.replicate 32 0) : LeanSpec.F) = toF zeros32
    rw [toF_zeros32]; rfl
  · unfold LeanSpec.feeSufficient; rw [he, hf]; simp [handlerWorld, toConfig, toyConfig]
  · unfold LeanSpec.pubAmtConsistent; rw [he, hf]
    refine ⟨fun _ => by omega, ?_⟩
    show toF one32 = _; rw [toF_one32]; simp
  · simp [LeanSpec.nullifiersFresh, handlerWorld]
  · show toF _ ≠ toF _
    rw [hk0, hk1, toF_zeros32, toF_one32]; exact h10.symm
  · intro _; rw [he]; show (1 : ℤ) ≤ (toyTree.max_deposit_amount.val : ℤ); simp [toyTree]
  · unfold LeanSpec.poolSolvent; rw [he, hf]
    exact ⟨fun h => by omega, fun h => by omega⟩
  · unfold LeanSpec.signerSolvent; rw [he]; simp [handlerWorld, toyState]
  · show toyTree.next_index.val ≤ 2 ^ 26 - 2; simp [toyTree]
  · unfold LeanSpec.amountsInRange; rw [he, hf]; norm_num
  · simp [LeanSpec.encOutsFit, toInputs, emptySlice, toBytes]
  · refine ⟨fun e => pk_ne (by decide : (1#u8 : U8) ≠ 2#u8) (toPubkey_inj e), fun h => ?_, fun h => ?_⟩
    · rw [he] at h; omega
    · rw [hf] at h; omega
  · intro i
    show LeanSpec.canonicalEncoding (toBytes ((publicInputs _)[i.val]!).val) _
    rw [canonicalEncoding_iff]
    fin_cases i
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_one32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
    · exact ⟨canonical_zeros32, rfl⟩
  · refine ⟨fun k _ => ?_, fun _ => ?_⟩
    · have hb : (handlerWorld toyAccounts (toyState 1#u64) 0#u64 toyTree toyConfig ∅).balances k = 1 := by
        simp [handlerWorld, toyState]
      rw [hb]
      unfold LeanSpec.balanceDelta
      rw [he, hf]
      split_ifs <;> norm_num
    · show ((handlerWorld toyAccounts (toyState 1#u64) 0#u64 toyTree toyConfig ∅).balances _ : ℤ) + _ < _
      rw [he]; simp [handlerWorld, toyState]


/-- L1: the toy internal transfer is rejected (`check_public_amount` rejects `extAmt = 0`). -/
theorem toy_L1_rejects (ap : transact.Appended) (e : SolEnv) (t : merkle_tree.MerkleTreeAccount) :
    transact.transact toyCrypto.hasher arkFr toyCrypto.sha256 toyCrypto.proofVerifier solRuntime
      (handlerEnv toyAccounts (toyState 0#u64) 0#u64) toyTree toyConfig
      (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32) 0#i64 0#u64
      toyAccounts.recipient toyAccounts.feeRecipientAccount emptySlice emptySlice ≠ ok (.Ok ap, e, t) := by
  intro h
  have h2 := (handler_ok toyCrypto _ _ _ _ _ _ _ _ _ _ _ _ _ h).pubAmt
  have h3 : utils.check_public_amount arkFr 0#i64 0#u64
      (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32).public_amount = ok false :=
    checkPublicAmount_L1.1
  rw [h3] at h2; simp at h2

/-- A0: the toy deposit with `proof_a` the 64 zero bytes is rejected by the verifier. -/
theorem toy_A0_rejects (ap : transact.Appended) (e : SolEnv) (t : merkle_tree.MerkleTreeAccount) :
    transact.transact toyCrypto.hasher arkFr toyCrypto.sha256 toyCrypto.proofVerifier solRuntime
      (handlerEnv toyAccounts (toyState 1#u64) 0#u64) toyTree toyConfig
      (toyProof zeros64 one32) 1#i64 0#u64
      toyAccounts.recipient toyAccounts.feeRecipientAccount emptySlice emptySlice ≠ ok (.Ok ap, e, t) := by
  intro h
  have h2 := (handler_ok toyCrypto _ _ _ _ _ _ _ _ _ _ _ _ _ h).verify
  have h3 : toyCrypto.proofVerifier.verify (toyProof zeros64 one32) = ok false :=
    verifyProof_zeroA (toyProof zeros64 one32) _ (by simp [toyProof, zeros64, Std.Array.repeat_val])
  rw [h3] at h2; simp at h2

/-- The faithful statement, instantiated at the L1 toy transaction, is false. -/
theorem toy_refutes_L1 {Q : transact.Appended → SolEnv → merkle_tree.MerkleTreeAccount → Prop}
    (h : HandlerPre Unit Unit Unit toyCrypto toyC toyLaws toyAccounts (toyState 0#u64) 0#u64 toyTree
      toyConfig ∅ (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32) 0#i64 0#u64 emptySlice emptySlice →
      ∃ ap e t, transact.transact toyCrypto.hasher arkFr toyCrypto.sha256 toyCrypto.proofVerifier solRuntime
        (handlerEnv toyAccounts (toyState 0#u64) 0#u64) toyTree toyConfig
        (toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32) 0#i64 0#u64
        toyAccounts.recipient toyAccounts.feeRecipientAccount emptySlice emptySlice = ok (.Ok ap, e, t) ∧
        Q ap e t) : False := by
  obtain ⟨ap, e, t, hh, -⟩ := h toy_pre_L1
  exact toy_L1_rejects ap e t hh

/-- The statement excluding only L1, instantiated at the A0 toy transaction, is false. -/
theorem toy_refutes_A0 {Q : transact.Appended → SolEnv → merkle_tree.MerkleTreeAccount → Prop}
    (h : HandlerPre Unit Unit Unit toyCrypto toyC toyLaws toyAccounts (toyState 1#u64) 0#u64 toyTree
      toyConfig ∅ (toyProof zeros64 one32) 1#i64 0#u64 emptySlice emptySlice →
      ∃ ap e t, transact.transact toyCrypto.hasher arkFr toyCrypto.sha256 toyCrypto.proofVerifier solRuntime
        (handlerEnv toyAccounts (toyState 1#u64) 0#u64) toyTree toyConfig
        (toyProof zeros64 one32) 1#i64 0#u64
        toyAccounts.recipient toyAccounts.feeRecipientAccount emptySlice emptySlice = ok (.Ok ap, e, t) ∧
        Q ap e t) : False := by
  obtain ⟨ap, e, t, hh, -⟩ := h toy_pre_A0
  exact toy_A0_rejects ap e t hh

/-- The toy proof of the L1 counterexample (an internal transfer). -/
abbrev l1Proof : transact.Proof := toyProof verifying_key.VERIFYING_KEY.vk_alpha_g1 zeros32
/-- The toy proof of the A0 counterexample (`proof_a` the 64 zero bytes). -/
abbrev a0Proof : transact.Proof := toyProof zeros64 one32

/-- The toy deployment satisfies the completeness assumptions. -/
theorem toyAssumptions : CompletenessAssumptions toyCrypto toyC :=
  ⟨toyHashesAgree, toyHashesSucceed, toySyscalls, toyKey⟩

/-- The toy handler context holds. -/
theorem toyContext (n : U64) :
    HandlerContext toyAccounts (toyState n) toyTree toyConfig emptySlice emptySlice :=
  ⟨toyTree_shape, toyTree_hist, toyTree_sub, by simp [toyConfig], by simp [toyConfig],
    by simp [toyConfig], ⟨rfl, rfl⟩, toyFit⟩

end Connection.Toy
