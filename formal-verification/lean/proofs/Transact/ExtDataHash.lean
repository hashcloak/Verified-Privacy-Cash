import code_model.generated.Funs
open Aeneas Aeneas.Std Result ControlFlow
namespace zkcash

/-! Writing into a `Vec<u8>`: each borsh encoder appends exactly its bytes and succeeds. -/

@[step]
theorem wrBytes_vecU8_spec (A : Type) (l : List Std.U8) (w : alloc.vec.Vec Std.U8)
    (h : l.length ≤ Usize.max) (hfit : w.val.length + l.length ≤ Usize.max) :
    wrBytes (alloc.vec.VecU8.Insts.StdIoWrite A) l w h ⦃ r w' => r = .Ok () ∧ w'.val = w.val ++ l ⦄ := by
  simp only [wrBytes, alloc.vec.VecU8.Insts.StdIoWrite.write]
  simp [hfit]

@[step]
theorem pubkey_serialize_vecU8_spec (A : Type) (pk : solana_pubkey.Pubkey) (w : alloc.vec.Vec Std.U8)
    (hfit : w.val.length + 32 ≤ Usize.max) :
    solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize.serialize (alloc.vec.VecU8.Insts.StdIoWrite A) pk w
      ⦃ r w' => r = .Ok () ∧ w'.val = w.val ++ pk.val ⦄ := by
  unfold solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize.serialize
  have := pk.property
  step*

@[step]
theorem u64_serialize_vecU8_spec (A : Type) (x : Std.U64) (w : alloc.vec.Vec Std.U8)
    (hfit : w.val.length + 8 ≤ Usize.max) :
    U64.Insts.BorshSerBorshSerialize.serialize (alloc.vec.VecU8.Insts.StdIoWrite A) x w
      ⦃ r w' => r = .Ok () ∧ w'.val = w.val ++ leBytes 8 x.val ⦄ := by
  unfold U64.Insts.BorshSerBorshSerialize.serialize
  step*

@[step]
theorem i64_serialize_vecU8_spec (A : Type) (x : Std.I64) (w : alloc.vec.Vec Std.U8)
    (hfit : w.val.length + 8 ≤ Usize.max) :
    I64.Insts.BorshSerBorshSerialize.serialize (alloc.vec.VecU8.Insts.StdIoWrite A) x w
      ⦃ r w' => r = .Ok () ∧ w'.val = w.val ++ leBytes 8 (x.val % (2 ^ 64 : Int)).toNat ⦄ := by
  unfold I64.Insts.BorshSerBorshSerialize.serialize
  step*

theorem borshSerList_u8_spec (A : Type) (l : List Std.U8) (w : alloc.vec.Vec Std.U8)
    (hfit : w.val.length + l.length ≤ Usize.max) :
    borshSerList U8.Insts.BorshSerBorshSerialize (alloc.vec.VecU8.Insts.StdIoWrite A) l w
      ⦃ r w' => r = .Ok () ∧ w'.val = w.val ++ l ⦄ := by
  induction l generalizing w with
  | nil => simp [borshSerList]
  | cons x xs ih =>
    simp only [borshSerList, U8.Insts.BorshSerBorshSerialize, U8.Insts.BorshSerBorshSerialize.serialize]
    have hx := wrBytes_vecU8_spec A [x] w (by simp; scalar_tac) (by simp at hfit ⊢; omega)
    obtain ⟨⟨r, w1⟩, heq, hr, hw1⟩ := WP.spec_imp_exists hx
    rw [heq]; simp only [bind_tc_ok, hr]
    apply WP.spec_mono (ih w1 (by simp at hfit; rw [hw1]; simp; omega))
    rintro ⟨r2, w2⟩ ⟨hr2, hw2⟩
    exact ⟨hr2, by rw [hw2, hw1]; simp⟩

@[step]
theorem vecU8_serialize_vecU8_spec (A : Type) (v : alloc.vec.Vec Std.U8) (w : alloc.vec.Vec Std.U8)
    (hv : v.val.length < 2 ^ 32) (hfit : w.val.length + 4 + v.val.length ≤ Usize.max) :
    alloc.vec.Vec.Insts.BorshSerBorshSerialize.serialize U8.Insts.BorshSerBorshSerialize
      (alloc.vec.VecU8.Insts.StdIoWrite A) v w
      ⦃ r w' => r = .Ok () ∧ w'.val = w.val ++ leBytes 4 v.val.length ++ v.val ⦄ := by
  unfold alloc.vec.Vec.Insts.BorshSerBorshSerialize.serialize
  have hv' : v.length < 2 ^ 32 := hv
  simp only [hv', if_true]
  have hx := wrBytes_vecU8_spec A (leBytes 4 v.length) w (by simp [leBytes]; scalar_tac) (by simp [leBytes]; omega)
  obtain ⟨⟨r, w1⟩, heq, hr, hw1⟩ := WP.spec_imp_exists hx
  rw [heq]; simp only [bind_tc_ok, hr]
  apply WP.spec_mono (borshSerList_u8_spec A v.val w1 (by rw [hw1]; simp [leBytes]; omega))
  rintro ⟨r2, w2⟩ ⟨hr2, hw2⟩
  exact ⟨hr2, by rw [hw2, hw1]⟩

/-! The ext-data hash preimage. -/

/-- The bytes `calculate_complete_ext_data_hash` hashes: the borsh encoding of
    `CompleteExtData`, laid out field by field.

    | bytes | field               | encoding                                   |
    |-------|---------------------|--------------------------------------------|
    | 32    | recipient           | raw                                        |
    | 8     | ext_amount          | little-endian, two's complement            |
    | 4     | len(encrypted_output1) | little-endian count                     |
    | n₁    | encrypted_output1   | raw                                        |
    | 4     | len(encrypted_output2) | little-endian count                     |
    | n₂    | encrypted_output2   | raw                                        |
    | 8     | fee                 | little-endian                              |
    | 32    | fee_recipient       | raw                                        |
    | 32    | mint_address        | raw                                        | -/
def extDataPreimage (recipient : solana_pubkey.Pubkey) (ext_amount : Std.I64)
    (encrypted_output1 encrypted_output2 : List Std.U8) (fee : Std.U64)
    (fee_recipient mint_address : solana_pubkey.Pubkey) : List Std.U8 :=
  recipient.val ++ leBytes 8 (ext_amount.val % (2 ^ 64 : Int)).toNat ++
  leBytes 4 encrypted_output1.length ++ encrypted_output1 ++
  leBytes 4 encrypted_output2.length ++ encrypted_output2 ++
  leBytes 8 fee.val ++ fee_recipient.val ++ mint_address.val

theorem extDataPreimage_length (recipient : solana_pubkey.Pubkey) (ext_amount : Std.I64)
    (e1 e2 : List Std.U8) (fee : Std.U64) (fee_recipient mint_address : solana_pubkey.Pubkey) :
    (extDataPreimage recipient ext_amount e1 e2 fee fee_recipient mint_address).length =
      120 + e1.length + e2.length := by
  simp [extDataPreimage, leBytes, recipient.property, fee_recipient.property, mint_address.property]
  omega

theorem completeExtData_serialize_spec (A : Type) (d : utils.calculate_complete_ext_data_hash.CompleteExtData)
    (w : alloc.vec.Vec Std.U8)
    (h1 : d.encrypted_output1.val.length < 2 ^ 32) (h2 : d.encrypted_output2.val.length < 2 ^ 32)
    (hfit : w.val.length + 120 + d.encrypted_output1.val.length + d.encrypted_output2.val.length ≤ Usize.max) :
    utils.calculate_complete_ext_data_hash.CompleteExtData.Insts.BorshSerBorshSerialize.serialize
      solana_pubkey.Pubkey.Insts.BorshSerBorshSerialize I64.Insts.BorshSerBorshSerialize
      (alloc.vec.Vec.Insts.BorshSerBorshSerialize U8.Insts.BorshSerBorshSerialize) U64.Insts.BorshSerBorshSerialize
      (alloc.vec.VecU8.Insts.StdIoWrite A) d w
      ⦃ r w' => r = .Ok () ∧ w'.val = w.val ++ extDataPreimage d.recipient d.ext_amount
          d.encrypted_output1.val d.encrypted_output2.val d.fee d.fee_recipient d.mint_address ⦄ := by
  unfold utils.calculate_complete_ext_data_hash.CompleteExtData.Insts.BorshSerBorshSerialize.serialize
  step* <;> first
    | (simp_all [extDataPreimage]; done)
    | (simp_all [leBytes]; omega)

/-- `calculate_complete_ext_data_hash` is SHA-256 of `extDataPreimage`, and nothing else: it
    never takes an error branch and never fails, provided each encrypted output is shorter than
    2^32 bytes (borsh's length prefix) and the whole preimage fits in a `usize` -- both far beyond
    what fits in a Solana transaction. SHA-256 itself stays abstract, so the statement is
    "whatever SHA-256 returns on these bytes". -/
theorem calculate_complete_ext_data_hash_spec (recipient : solana_pubkey.Pubkey) (ext_amount : Std.I64)
    (encrypted_output1 encrypted_output2 : Slice Std.U8) (fee : Std.U64)
    (fee_recipient mint_address : solana_pubkey.Pubkey)
    (h1 : encrypted_output1.val.length < 2 ^ 32) (h2 : encrypted_output2.val.length < 2 ^ 32)
    (hlen : (extDataPreimage recipient ext_amount encrypted_output1.val encrypted_output2.val fee
      fee_recipient mint_address).length ≤ Usize.max) :
    utils.calculate_complete_ext_data_hash recipient ext_amount encrypted_output1 encrypted_output2 fee
        fee_recipient mint_address =
      (do
        let h ← solana_sha256_hasher.hash ⟨extDataPreimage recipient ext_amount encrypted_output1.val
          encrypted_output2.val fee fee_recipient mint_address, hlen⟩
        ok (.Ok h)) := by
  unfold utils.calculate_complete_ext_data_hash
  have hclone : ∀ (s : Slice Std.U8),
      alloc.slice.Slice.to_vec core.clone.CloneU8 s = ok (⟨s.val, s.property⟩ : alloc.vec.Vec Std.U8) := by
    intro s
    obtain ⟨s', hs', hss'⟩ := WP.spec_imp_exists
      (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (by intro x _; rfl))
    subst hss'; exact hs'
  rw [hclone, hclone]
  simp only [Bind.bind, Aeneas.Std.bind]
  have hfit := hlen
  rw [extDataPreimage_length] at hfit
  obtain ⟨⟨r, w⟩, heq, hr, hw⟩ := WP.spec_imp_exists
    (completeExtData_serialize_spec Global
      { recipient, ext_amount, encrypted_output1 := ⟨encrypted_output1.val, encrypted_output1.property⟩,
        encrypted_output2 := ⟨encrypted_output2.val, encrypted_output2.property⟩,
        fee, fee_recipient, mint_address } (alloc.vec.Vec.new Std.U8) h1 h2 (by simp; omega))
  simp only [heq, hr, uncurry, core.result.Result.Insts.CoreOpsTry.branch, solana_hash.Hash.to_bytes]
  have hderef : alloc.vec.Vec.deref w = ⟨extDataPreimage recipient ext_amount encrypted_output1.val
      encrypted_output2.val fee fee_recipient mint_address, hlen⟩ := by
    apply Subtype.ext; simpa [alloc.vec.Vec.deref] using hw
  rw [hderef]
