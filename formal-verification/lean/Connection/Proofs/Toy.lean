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
theorem toF_zeros32 : toF zeros32 = 0 := by simp only [toF_def, beNat_zeros32, Nat.cast_zero]
theorem toF_one32 : toF one32 = 1 := by simp only [toF_def, beNat_one32, Nat.cast_one]
theorem canonical_zeros32 : Canonical zeros32 := by
  simp only [canonical_def, beNat_zeros32]; decide
theorem canonical_one32 : Canonical one32 := by
  simp only [canonical_def, beNat_one32]; decide

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
    | none => exact absurd (by simp [g1At, toyC, hd]) h
    | some _ => rfl
  add := by
    intro input h1 h2
    refine ⟨zeros64, ?_⟩
    simp only [toyAltBn]
    rw [if_pos]
    simp only [Bool.and_eq_true]
    constructor
    · cases hd : syscallDecodeG1 (bytesAt input 0 64#usize (by simp)) with
      | none => exact absurd (by simp [g1At, toyC, hd]) h1
      | some _ => rfl
    · cases hd : syscallDecodeG1 (bytesAt input 64 64#usize (by simp)) with
      | none => exact absurd (by simp [g1At, toyC, hd]) h2
      | some _ => rfl
  pairing := by
    intro input P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ d1 _ d2 _ d3 _ d4 _
    refine ⟨one32, ?_, ?_⟩
    · simp only [toyAltBn]
      rw [if_pos]
      simp only [pairingG1Decode, Bool.and_eq_true]
      simp only [g1At, toyC, Option.map_eq_some_iff] at d1 d2 d3 d4
      obtain ⟨_, h1, -⟩ := d1; obtain ⟨_, h2, -⟩ := d2
      obtain ⟨_, h3, -⟩ := d3; obtain ⟨_, h4, -⟩ := d4
      simp [h1, h2, h3, h4]
    · exact ⟨fun _ => rfl, fun _ => by decide⟩

theorem toyLaws : PairingLaws toyC.e :=
  ⟨fun _ _ => rfl⟩

theorem toyKey : KeyG2Decodes toyC := ⟨by simp [toyC], by simp [toyC], by simp [toyC]⟩

/-! The spec's groups, pairing and key for the toy deployment, as the connection theorems fix
them (`syscallGroups`, `syscallPairing`, `programKey`), with the group structure of `Unit`. Used
as local instances by statements about the toy. -/

section
@[reducible] def toySpecGroups : Spec.Groups := syscallGroups toyC
attribute [local instance] toySpecGroups
@[reducible] def toySpecG1Group : AddCommGroup Spec.G1 := inferInstanceAs (AddCommGroup Unit)
attribute [local instance] toySpecG1Group
@[reducible] def toySpecG1Module : Module Spec.F Spec.G1 := inferInstanceAs (Module Spec.F Unit)
@[reducible] def toySpecGTGroup : CommGroup Spec.GT := inferInstanceAs (CommGroup Unit)
attribute [local instance] toySpecG1Module toySpecGTGroup
@[reducible] def toySpecPairing : Spec.Pairing := syscallPairing toyC
@[reducible] def toySpecDeployment : Spec.Deployment := programDeployment toyC
end

/-! ## The hashes -/

/-- The zero hashes: `0`, then `1` (Poseidon always returns 1). -/
def toyZ : Std.Array (Std.Array U8 32#usize) 41#usize :=
  Std.Array.make 41#usize (zeros32 :: List.replicate 40 one32) (by simp)

def toyHasher : merkle_tree.Hasher Unit := ⟨fun _ _ => ok one32, ok toyZ⟩
def toySha256 : ext_data.Sha256 Unit := ⟨fun _ => ok zeros32⟩
@[reducible] def toyCrypto : Crypto := ⟨toyHasher, toySha256, toyAltBn⟩

def pk (n : U8) : Pubkey := Std.Array.make 32#usize (n :: List.replicate 31 0#u8) (by simp)

/-- Toy address derivation of the seeds: distinguishes the inputs the toy run uses (length, the
    slot byte of the nullifier seeds, the last nullifier byte); marked 170 in byte 0 so it never is a
    `pk n`. -/
def toyCPA (l : List U8) : Pubkey :=
  Std.Array.make 32#usize ([170#u8, ⟨BitVec.ofNat 8 l.length⟩, l.getD 9 0#u8, l.getD 41 0#u8] ++
    List.replicate 28 0#u8) (by simp)

def toyD : Deployment :=
  { programId := pk 100#u8, createProgramAddress := toyCPA, canonicalBump := fun _ => 255#u8,
    crypto := toyCrypto, adminPubkey := none }

/-- Spec instances matching the toy hashes: `H2` is constant 1, `sha256` returns 32 zero bytes.
    The code never computes `H1`, `H3`, `H4` (only the circuit does); they are chosen so that
    the toy run's transactions have circuit witnesses (`Proofs/ToyRun.lean`): `H1` is the
    identity, `H3` and `H4` add their arguments. -/
@[reducible] def toyPoseidon : Spec.PoseidonHashes :=
  ⟨fun a => a, fun _ _ => 1, fun a b c => a + b + c, fun a b c d => a + b + c + d⟩
@[reducible] def toySpecSha : Spec.Sha := ⟨fun _ => toBytes zeros32.val⟩

attribute [local instance] toyPoseidon toySpecSha

/-- The toy SHA-256 of a transaction's external data: 32 zero bytes. -/
theorem toy_extDataHash {inputs : Spec.TxInputs} :
    Spec.Sha.sha256 (Spec.serealizeExternalData inputs) = toBytes zeros32.val := rfl

theorem toyZ_zero : toyZ.val[0]! = zeros32 := by rfl
theorem toyZ_succ (i : ℕ) (hi : i < 40) : toyZ.val[i + 1]! = one32 := by
  show (zeros32 :: List.replicate 40 one32)[i + 1]! = one32
  rw [getElem!_pos _ _ (by simp only [List.length_cons, List.length_replicate]; omega),
    List.getElem_cons_succ, List.getElem_replicate]

theorem toyZ_canonical (i : ℕ) (hi : i ≤ 26) : Canonical (toyZ.val[i]!) := by
  cases i with
  | zero => rw [toyZ_zero]; exact canonical_zeros32
  | succ i => rw [toyZ_succ i (by omega)]; exact canonical_one32

theorem spec_Z (i : ℕ) : Spec.Z i = if i = 0 then 0 else 1 := by
  cases i <;> rfl

theorem toyHashesAgree : HashesAgree toyD where
  poseidon := by
    intro a b h _ _ hh
    obtain rfl := (Result.ok_injective hh).symm
    refine ⟨canonical_one32, ?_⟩
    rw [toF_one32]; rfl
  zeroBytes := ⟨toyZ, rfl, fun i hi => ⟨toyZ_canonical i hi, by
    rw [spec_Z]
    cases i with
    | zero => rw [toyZ_zero, toF_zeros32]; rfl
    | succ i => rw [toyZ_succ i (by omega), toF_one32]; rfl⟩⟩
  sha256 := by
    intro x h hh
    obtain rfl := (Result.ok_injective hh).symm
    rfl

theorem toyPoseidonSucceeds : PoseidonSucceeds toyCrypto :=
  ⟨fun _ _ _ _ => ⟨one32, rfl⟩⟩

/-! ## A toy transaction, for the handler -/

def toyProof (pa : Std.Array U8 64#usize) (pubAmt : Std.Array U8 32#usize) : transact.Proof :=
  { proof_a := pa, proof_b := Std.Array.repeat 128#usize 0#u8, proof_c := zeros64,
    root := one32, public_amount := pubAmt, ext_data_hash := zeros32,
    input_nullifiers := Std.Array.make 2#usize [zeros32, one32] (by simp),
    output_commitments := Std.Array.make 2#usize [zeros32, zeros32] (by simp) }

def emptySlice : Slice U8 := Slice.from [] (by simp)

theorem pk_ne {m n : U8} (h : m ≠ n) : pk m ≠ pk n := by
  intro e
  have := congrArg (fun a : Pubkey => a.val[0]!) e
  simp [pk, Std.Array.make] at this
  exact h this


/-- The nullifier accounts' addresses the handler examples give the spec: the transaction's own
    two nullifier accounts. -/
def handlerAddr (a : TransactAccounts) : Fin 2 → Spec.Bytes → Spec.Pubkey :=
  fun i _ => toPubkey (![a.nullifier0, a.nullifier1] i)

/-- In a handler example, the new nullifier accounts are the transaction's own, so the spec's
    address checks are the accounts' distinctness. -/
theorem handlerAddr_facts
    (signers : List Pubkey) (a : TransactAccounts) (proof : transact.Proof) (ext : I64) (fee : U64)
    (out1 out2 : Slice U8) (s₁ : State) (v : U64) (tree : merkle_tree.MerkleTreeAccount)
    (config : admin.GlobalConfig) (accts : Finset Spec.Pubkey)
    (h01 : a.nullifier0 ≠ a.nullifier1) (h0p : a.nullifier0 ≠ a.treeTokenAccount)
    (h1p : a.nullifier1 ≠ a.treeTokenAccount) (hs0 : a.signer ≠ a.nullifier0)
    (hs1 : a.signer ≠ a.nullifier1) (hsp : a.signer ≠ a.treeTokenAccount)
    (h0t : a.nullifier0 ≠ a.treeAccount) (h0c : a.nullifier0 ≠ a.globalConfig)
    (h1t : a.nullifier1 ≠ a.treeAccount) (h1c : a.nullifier1 ≠ a.globalConfig)
    (hst : a.signer ≠ a.treeAccount) (hsc : a.signer ≠ a.globalConfig)
    (hacc : accts = ∅) :
    Spec.nullifierAccountsCreatable (handlerWorld a s₁ v tree config accts (handlerAddr a)).state
        (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩) ∧
      Spec.signerNotPoolNotNullifiers (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩)
        (handlerWorld a s₁ v tree config accts (handlerAddr a)).state := by
  have inj : ∀ {x y : Pubkey}, x ≠ y → toPubkey x ≠ toPubkey y := fun h e => h (toPubkey_inj e)
  subst hacc
  refine ⟨⟨inj h01, ?_, ?_⟩, ?_, inj hs0, inj hs1⟩
  · rintro (e | e | e | e)
    exacts [inj h0p e, Finset.notMem_empty _ e, inj h0t e, inj h0c e]
  · rintro (e | e | e | e)
    exacts [inj h1p e, Finset.notMem_empty _ e, inj h1t e, inj h1c e]
  · rintro (e | e | e | e)
    exacts [inj hsp e, Finset.notMem_empty _ e, inj hst e, inj hsc e]
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
def HandlerPre (G1 G2 GT : Type) [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
    [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
    (signers : List Pubkey) (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (a : TransactAccounts) (s₁ : State) (v : U64) (tree : merkle_tree.MerkleTreeAccount)
    (config : admin.GlobalConfig) (accts : Finset Spec.Pubkey)
    (addr : Fin 2 → Spec.Bytes → Spec.Pubkey) (proof : transact.Proof)
    (ext : I64) (fee : U64) (out1 out2 : Slice U8) : Prop :=
  @Spec.transactPreconditions _ (syscallGroups C) (inferInstanceAs (AddCommGroup G1))
    (inferInstanceAs (Module Spec.F G1))
    (inferInstanceAs (CommGroup GT))
    (syscallPairing C) (programDeployment C) (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩)
    (handlerWorld a s₁ v tree config accts addr)

/-- The toy deployment's primitives return a value on valid input. -/
theorem toySha256Succeeds : ∀ x, ∃ h, toySha256.hash x = ok h := fun _ => ⟨zeros32, rfl⟩

theorem toyCryptoSucceeds : CryptoSucceeds toyCrypto toyC :=
  ⟨toyPoseidonSucceeds, toySha256Succeeds, toySyscalls, toyKey⟩

end Connection.Toy
