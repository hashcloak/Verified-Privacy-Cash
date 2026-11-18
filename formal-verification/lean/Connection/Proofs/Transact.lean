import Connection.Proofs.Collisions
import Connection.Proofs.Invariant
import Connection.Proofs.Handler
import Connection.Proofs.ExtData
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proof of the connection theorem for `transact`

NOT FOR REVIEW: the statement is restated in `Connection/ConnectionTheorems.lean`. -/

namespace Connection

/-! ## Balances: `moveN` and the address bijection -/

theorem moveN_other (B : Pubkey → ℕ) {u v k : Pubkey} (n : ℕ) (hu : k ≠ u) (hv : k ≠ v) :
    moveN B u v n k = B k := by
  simp [moveN, Function.update_of_ne hu, Function.update_of_ne hv]

theorem moveN_congr {B B' : Pubkey → ℕ} {R : Pubkey → Prop} (hBB : ∀ j, R j → B j = B' j)
    {u v : Pubkey} (hu : R u) (hv : R v) (n : ℕ) : ∀ j, R j → moveN B u v n j = moveN B' u v n j := by
  intro j hj
  simp only [moveN, Function.update]
  by_cases h1 : j = v <;> by_cases h2 : j = u <;> by_cases h3 : v = u <;>
    simp [h1, h2, h3, hBB u hu, hBB v hv, hBB j hj]

theorem leBytes32_leNat (l : List U8) (hl : l.length = 32) : leBytes32 (leNatOfList l) = l := by
  have hlt : leNatOfList l < 256 ^ 32 := by have := leNatOfList_lt l; rwa [hl] at this
  apply toBytes_inj
  have h1 := natToBytesLE_leNat (leBytes32 (leNatOfList l))
  have h2 := natToBytesLE_leNat l
  rw [PrivacyCash.Proofs.G1.leBytes32_length, PrivacyCash.Proofs.G1.leNat_leBytes32 _ hlt] at h1
  rw [hl] at h2
  rw [← h1, ← h2]

theorem fromPubkey_toPubkey (k : Pubkey) : fromPubkey (toPubkey k) = k := by
  have hl : k.val.length = 32 := by simp
  have hlt : leNatOfList k.val < 2 ^ 256 := by
    have := leNatOfList_lt k.val; rw [hl] at this; simpa using this
  apply (Std.Array.eq_iff _ _).mpr
  simp only [fromPubkey, toPubkey_def, Std.Array.from_val, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact leBytes32_leNat _ hl

theorem toPubkey_fromPubkey (x : Spec.Pubkey) : toPubkey (fromPubkey x) = x := by
  have hlt : x.toNat < 256 ^ 32 := by have := x.isLt; simpa using this
  apply BitVec.eq_of_toNat_eq
  simp only [toPubkey_def, fromPubkey, Std.Array.from_val, PrivacyCash.Proofs.G1.leNat_leBytes32 _ hlt,
    BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

theorem toPubkey_inj {k k' : Pubkey} (h : toPubkey k = toPubkey k') : k = k' := by
  rw [← fromPubkey_toPubkey k, h, fromPubkey_toPubkey]

theorem update_fromPubkey (B : Pubkey → ℕ) (u : Pubkey) (w : ℕ) :
    (fun x => Function.update B u w (fromPubkey x))
      = Function.update (fun x => B (fromPubkey x)) (toPubkey u) w := by
  funext x
  by_cases h : x = toPubkey u
  · subst h; simp [fromPubkey_toPubkey]
  · have : fromPubkey x ≠ u := fun e => h (by rw [← e, toPubkey_fromPubkey])
    simp [Function.update_of_ne h, Function.update_of_ne this]

theorem moveLamports_fromPubkey (B : Pubkey → ℕ) (u v : Pubkey) (n : ℕ) :
    Spec.moveLamports (fun x => B (fromPubkey x)) (toPubkey u) (toPubkey v) n
      = fun x => moveN B u v n (fromPubkey x) := by
  have := congrFun (update_fromPubkey B u (B u - n)) (toPubkey v)
  simp only [fromPubkey_toPubkey] at this
  simp only [Spec.moveLamports, moveN, fromPubkey_toPubkey]
  rw [← this, update_fromPubkey, update_fromPubkey]

/-! ## Small facts for the preconditions -/

theorem natOfLE_toBytes (l : List U8) :
    Spec.natOfLE (toBytes l) = l.foldr (fun x acc => acc * 256 + x.val) 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [toBytes, List.map_cons, Spec.natOfLE, List.foldr_cons] at ih ⊢
    rw [ih]; simp; ring

theorem toBytes_toSlice (bs : Spec.Bytes) (h : bs.length ≤ Usize.max) :
    toBytes (toSlice bs).val = bs := by
  have h' : (bs.map (fun b => (⟨b⟩ : U8))).length ≤ Usize.max := by simpa using h
  simp only [toSlice, dif_pos h', Slice.from_val, toBytes, List.map_map]
  conv_rhs => rw [← List.map_id bs]
  rfl

theorem serLength (inputs : Spec.TxInputs) :
    (Spec.serealizeExternalData inputs).length = 120 + inputs.encOut0.length + inputs.encOut1.length := by
  simp [Spec.serealizeExternalData, Spec.PubkeyToBytes, Spec.i64LE, Spec.u64LE,
    Spec.vecU8, Spec.u32LE, Spec.natToBytesLE]
  omega

theorem lamportsOf_lt (s : State) (k : Pubkey) : s.lamports k < 2 ^ 64 := u64_lt _

/-! ## A world without nullifier rent (the world the handler sees) -/

theorem moveLamports_zero (b : Spec.Pubkey → ℕ) (u v : Spec.Pubkey) :
    Spec.moveLamports b u v 0 = b := by
  unfold Spec.moveLamports; simp

/-- With no nullifier rent, the rent step changes nothing. -/
theorem nullifierRentEffects_noRent (inputs : Spec.TxInputs) (W : Spec.World)
    (h : W.nullifierRent = 0) : Spec.nullifierRentEffects inputs W = W := by
  simp [Spec.nullifierRentEffects, Spec.World.nullifierTopUp, h, moveLamports_zero]
  rw [← h]

/-- With no nullifier rent, no top-up. -/
theorem nullifierTopUp_noRent (inputs : Spec.TxInputs) (W : Spec.World)
    (h : W.nullifierRent = 0) (i : Fin 2) : W.nullifierTopUp inputs i = 0 := by
  simp [Spec.World.nullifierTopUp, h]

/-- With no nullifier rent, what one transaction moves into or out of an account. -/
theorem balanceDelta_noRent (inputs : Spec.TxInputs) (W : Spec.World)
    (h : W.nullifierRent = 0) (k : Spec.Pubkey) :
    Spec.balanceDelta inputs W k =
      (if k = inputs.A ∧ inputs.extAmt < 0 then (inputs.extAmt.natAbs : ℤ) else 0)
      + (if k = inputs.t then (inputs.f : ℤ) else 0)
      - (if k = inputs.s ∧ inputs.extAmt > 0 then inputs.extAmt else 0)
      + (if k = W.state.pool then inputs.extAmt - inputs.f else 0) := by
  simp [Spec.balanceDelta, nullifierTopUp_noRent inputs W h]

/-! ## Nullifier accounts and their addresses -/

theorem toArray_toBytes {n : Usize} (a : Std.Array U8 n) : toArray n (toBytes a.val) = some a := by
  have hl : (toBytes a.val).length = n.val := by simp [toBytes]
  simp only [toArray, dif_pos hl, Option.some.injEq]
  apply (Std.Array.eq_iff _ _).mpr
  simp only [Std.Array.from_val, toBytes, List.map_map]
  conv_rhs => rw [← List.map_id a.val]
  rfl

theorem nullifierAddrOf_bytes (d : Deployment) (n : Pubkey) :
    nullifierAddrOf d 0 (toBytes n.val) = toPubkey (d.pda (nullifier0Seeds n)) ∧
    nullifierAddrOf d 1 (toBytes n.val) = toPubkey (d.pda (nullifier1Seeds n)) := by
  simp [nullifierAddrOf, Deployment.nullifierAddress, toArray_toBytes]

/-- The spec's addresses of a `transact`'s two new nullifier accounts are the code's PDAs. -/
theorem newNullifierAccount_toWorld (d : Deployment) (rent : Nat → U64) (s : State)
    (signers : List Pubkey) (a : TransactAccounts) (proof : zkcash_core.transact.Proof)
    (ext : I64) (fee : U64) (out1 out2 : Slice U8) :
    (toWorld d rent s).state.newNullifierAccount (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩) 0
        = toPubkey (d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!)) ∧
      (toWorld d rent s).state.newNullifierAccount (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩) 1
        = toPubkey (d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!)) := by
  have hby0 : (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩).nullifierBytes 0
      = toBytes proof.input_nullifiers.val[0]!.val := by
    simp [toInputs, Spec.TxInputs.nullifierBytes, publicInputs]
  have hby1 : (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩).nullifierBytes 1
      = toBytes proof.input_nullifiers.val[1]!.val := by
    simp [toInputs, Spec.TxInputs.nullifierBytes, publicInputs]
  refine ⟨?_, ?_⟩
  · show nullifierAddrOf d 0 _ = _; rw [hby0]; exact (nullifierAddrOf_bytes d _).1
  · show nullifierAddrOf d 1 _ = _; rw [hby1]; exact (nullifierAddrOf_bytes d _).2

theorem mem_nullifierAccountsOf {d : Deployment} {s : State} {x : Spec.Pubkey} :
    x ∈ nullifierAccountsOf d s ↔ d.IsNullifierAccount s (fromPubkey x) := by
  simp [nullifierAccountsOf]

/-- A system account is not a nullifier account. -/
theorem not_nullifierAccount_of_system {d : Deployment} {s : State} {k : Pubkey}
    (hns : d.programId ≠ systemProgram) (h : (s k).owner = systemProgram) :
    toPubkey k ∉ nullifierAccountsOf d s := by
  rw [mem_nullifierAccountsOf, fromPubkey_toPubkey]
  exact fun ⟨ho, _⟩ => hns (ho ▸ h)

/-! ## Lamport conservation: the runtime's check over the instruction's accounts -/

/-- The total of `b` over the distinct addresses of `keys`. -/
def TL (keys : List Pubkey) (b : Pubkey → ℕ) : ℤ := ∑ k ∈ keys.toFinset, (b k : ℤ)

theorem totalLamports_eq (s : State) (keys : List Pubkey) :
    (s.totalLamports keys : ℤ) = TL keys (fun k => (s k).lamports.val) := by
  unfold State.totalLamports TL
  have hfs : keys.dedup.toFinset = keys.toFinset := by
    ext x; simp [List.mem_dedup]
  rw [← hfs, List.sum_toFinset _ (List.nodup_dedup keys)]
  push_cast; rw [List.map_map]; rfl

theorem TL_update {keys : List Pubkey} {k : Pubkey} (hk : k ∈ keys) (b : Pubkey → ℕ) (v : ℕ) :
    TL keys (Function.update b k v) = TL keys b - b k + v := by
  unfold TL
  have hmem : k ∈ keys.toFinset := List.mem_toFinset.mpr hk
  rw [← Finset.add_sum_erase _ _ hmem, ← Finset.add_sum_erase _ (fun x => (b x : ℤ)) hmem]
  have : ∑ x ∈ keys.toFinset.erase k, ((Function.update b k v x : ℕ) : ℤ)
      = ∑ x ∈ keys.toFinset.erase k, (b x : ℤ) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  rw [this, Function.update_self]; ring

/-- A real move (`moveN`, the system program's transfer) conserves lamports. -/
theorem TL_moveN {keys : List Pubkey} {u v : Pubkey} (hu : u ∈ keys) (hv : v ∈ keys)
    (b : Pubkey → ℕ) {x : ℕ} (hx : x ≤ b u) : TL keys (moveN b u v x) = TL keys b := by
  simp only [moveN]
  rw [TL_update hv, TL_update hu]
  by_cases h : v = u
  · subst h; simp; omega
  · rw [Function.update_of_ne h]; push_cast; omega

/-- The code's payment (`payN`) conserves lamports, except that paying an account from itself
    creates `x` lamports. -/
theorem TL_payN {keys : List Pubkey} {p t : Pubkey} (hp : p ∈ keys) (ht : t ∈ keys)
    (b : Pubkey → ℕ) {x : ℕ} (hx : x ≤ b p) :
    TL keys (payN b p t x) = TL keys b + (if t = p then (x : ℤ) else 0) := by
  simp only [payN]
  rw [TL_update ht, TL_update hp]
  by_cases h : t = p
  · subst h; simp; omega
  · rw [Function.update_of_ne h, if_neg h]; push_cast; omega

/-- Without a balance check, a move can only add lamports (natural subtraction truncates). -/
theorem TL_moveN_ge {keys : List Pubkey} {u v : Pubkey} (hu : u ∈ keys) (hv : v ∈ keys)
    (b : Pubkey → ℕ) (x : ℕ) : TL keys b ≤ TL keys (moveN b u v x) := by
  simp only [moveN]
  rw [TL_update hv, TL_update hu]
  by_cases h : v = u
  · subst h; simp; omega
  · rw [Function.update_of_ne h]; omega

/-- A payment adds at least `x` lamports when it pays an account from itself. -/
theorem TL_payN_ge {keys : List Pubkey} {p t : Pubkey} (hp : p ∈ keys) (ht : t ∈ keys)
    (b : Pubkey → ℕ) (x : ℕ) :
    TL keys b + (if t = p then (x : ℤ) else 0) ≤ TL keys (payN b p t x) := by
  simp only [payN]
  rw [TL_update ht, TL_update hp]
  by_cases h : t = p
  · subst h; simp; omega
  · rw [Function.update_of_ne h, if_neg h]; omega

theorem payN_eq_moveN (b : Pubkey → ℕ) (p t : Pubkey) (x : ℕ) (h : t ≠ p ∨ x = 0) :
    payN b p t x = moveN b p t x := by
  rcases h with h | h
  · rw [moveN_eq_updates _ _ _ h]; rfl
  · subst h; rw [payN_zero, moveN_zero]

theorem checkBalanced_spec {s s₂ s' : State} {keys : List Pubkey}
    (h : checkBalanced s s₂ keys = .ok s') :
    s' = s₂ ∧ s₂.totalLamports keys = s.totalLamports keys := by
  unfold checkBalanced at h
  split at h
  · rename_i heq; exact ⟨(Except.ok.inj h).symm, heq⟩
  · cases h

theorem ofResult_ok {α : Type} {r : Result α} {x : α} (h : ofResult r = .ok x) : r = ok x := by
  unfold ofResult at h
  cases r with
  | ret a =>
    simp [Option.ofResult] at h
    rw [h]
  | vis e k => simp [Option.ofResult] at h
  | div => simp [Option.ofResult] at h

/-- Anchor `init` at an address holding no lamports: a system transfer of the rent from the
    payer, then the account becomes the program's, with the given data. -/
theorem initAccount_empty {pid : Pubkey} {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (hzero : (s key).lamports.val = 0)
    (h : s.initAccount pid mb payer key space data = some s') :
    (s payer).owner = systemProgram ∧ (s payer).data.isEmpty ∧ (mb space).val ≤ (s payer).lamports.val ∧
      (fun k => (s' k).lamports.val) = moveN (fun k => (s k).lamports.val) payer key (mb space).val ∧
      (s' key).owner = pid ∧ (s' key).data = data ∧
      (∀ k, k ≠ key → (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data) := by
  unfold State.initAccount at h
  simp only [hzero, if_true] at h
  cases hb : systemTransferBalances s s.balances payer key (mb space) with
  | none => simp [State.systemTransfer, hb] at h
  | some b =>
  simp only [State.systemTransfer, hb, Option.map_some, Option.some.injEq] at h
  subst h
  obtain ⟨ho, hd, hle, hv⟩ := stb_spec hb
  refine ⟨ho, hd, hle, ?_, by simp, by simp, fun k hk => by simp [State.set, hk]⟩
  funext k
  have := congrFun hv k
  by_cases hk : k = key
  · subst hk; simp [State.set, State.withBalances]; exact this
  · simp [State.set, hk, State.withBalances]; exact this

/-- `moveN` at a point of `R` only reads `R`. -/
theorem moveN_congr_at {B B' : Pubkey → ℕ} {R : Pubkey → Prop} (hBB : ∀ j, R j → B j = B' j)
    (u v : Pubkey) (n : ℕ) : ∀ j, R j → moveN B u v n j = moveN B' u v n j := by
  intro j hj
  simp only [moveN, Function.update]
  by_cases h1 : j = v <;> by_cases h2 : j = u <;> by_cases h3 : v = u <;> simp_all

theorem moveN_mono {B B' : Pubkey → ℕ} (hle : ∀ j, B j ≤ B' j) {u : Pubkey} (hu : B u = B' u)
    (v : Pubkey) (n : ℕ) : ∀ j, moveN B u v n j ≤ moveN B' u v n j := by
  intro j
  have := hle j; have := hle v
  simp only [moveN, Function.update]
  by_cases h1 : j = v <;> by_cases h2 : j = u <;> by_cases h3 : v = u <;> simp_all

theorem lamportsOf_le (s : State) (k : Pubkey) : s.lamports k ≤ (s k).lamports.val :=
  le_refl _

/-- Anchor `init`, in general: the payer tops the address up by `top` (the whole rent if the
    address is empty, possibly nothing if it already holds enough; with a positive rent, exactly
    what the address is missing), then the account becomes the program's, with the given data. -/
theorem initAccount_spec {pid : Pubkey} {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
    {space : Nat} {data : AccountData} (hpk : payer ≠ key)
    (h : s.initAccount pid mb payer key space data = some s') :
    ∃ top : ℕ, top ≤ (s payer).lamports.val ∧
      (0 < top → (s payer).owner = systemProgram ∧ (s payer).data.isEmpty) ∧
      ((s key).lamports.val = 0 → top = (mb space).val) ∧
      (0 < (mb space).val → top = (mb space).val - (s key).lamports.val) ∧
      (fun k => (s' k).lamports.val) = moveN (fun k => (s k).lamports.val) payer key top ∧
      (s' key).owner = pid ∧ (s' key).data = data ∧
      (∀ k, k ≠ key → (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data) := by
  by_cases hz : (s key).lamports.val = 0
  · obtain ⟨ho, hd, hle, hlam, hown, hdat, hoth⟩ := initAccount_empty hz h
    exact ⟨(mb space).val, hle, fun _ => ⟨ho, hd⟩, fun _ => rfl, fun _ => by rw [hz]; rfl,
      hlam, hown, hdat, hoth⟩
  unfold State.initAccount at h
  simp only [hz, if_false] at h
  simp only [hpk, if_false] at h
  have fin : ∀ s₂ : State, (fun k => (s₂ k).lamports.val) = moveN (fun k => (s k).lamports.val) payer key 0 ∨
      True → s' = s₂.set key { s₂ key with owner := pid, data := data } →
      (s' key).owner = pid ∧ (s' key).data = data ∧
      (∀ k, k ≠ key → (s' k).owner = (s₂ k).owner ∧ (s' k).data = (s₂ k).data) ∧
      (fun k => (s' k).lamports.val) = fun k => (s₂ k).lamports.val := by
    intro s₂ _ e; subst e
    refine ⟨by simp [State.set], by simp [State.set], fun k hk => by simp [State.set, hk], ?_⟩
    funext k; by_cases hk : k = key
    · subst hk; simp [State.set]
    · simp [State.set, hk]
  split at h
  · rename_i ht
    simp only [Option.map_some, Option.some.injEq] at h
    obtain ⟨hown, hdat, hoth, hlam⟩ := fin s (Or.inr trivial) h.symm
    exact ⟨0, Nat.zero_le _, fun h0 => absurd h0 (lt_irrefl 0), fun h0 => absurd h0 hz,
      fun hpos => by omega, by rw [hlam, moveN_zero], hown, hdat, hoth⟩
  · cases hb : systemTransferBalances s s.balances payer key ⟨BitVec.ofNat 64 ((max (mb space).val 1) - (s key).lamports.val)⟩ with
    | none => simp [State.systemTransfer, hb] at h
    | some b =>
    simp only [State.systemTransfer, hb, Option.map_some, Option.some.injEq] at h
    obtain ⟨ho, hd, hle, hv⟩ := stb_spec hb
    obtain ⟨hown, hdat, hoth, hlam⟩ := fin _ (Or.inr trivial) h.symm
    refine ⟨_, hle, fun _ => ⟨ho, hd⟩, fun h0 => absurd h0 hz, fun hpos => ?_, ?_, hown, hdat,
      fun k hk => by obtain ⟨a1, a2⟩ := hoth k hk; exact ⟨a1, a2⟩⟩
    · have hlt := u64_lt (mb space)
      show (BitVec.ofNat 64 ((max (mb space).val 1) - (s key).lamports.val)).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [hlam]; funext k
    have := congrFun hv k
    simpa [State.withBalances, State.balances] using this

/-- The accounts of a `transact` instruction, over which the runtime checks conservation. -/
def txKeys (a : TransactAccounts) : List Pubkey :=
  [a.treeAccount, a.nullifier0, a.nullifier1, a.nullifier2, a.nullifier3, a.treeTokenAccount,
   a.globalConfig, a.recipient, a.feeRecipientAccount, a.signer, a.systemProgram]

/-- What a successful `execTransact` consists of. -/
theorem execTransact_ok {d : Deployment} {s s' : State} {tx : TxEnv} {a : TransactAccounts}
    {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64} {out1 out2 : Slice U8}
    {evs : List CommitmentData}
    (h : execTransact d s tx a proof ext fee out1 out2 = .ok (s', evs)) :
    ∃ (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (tt : zkcash_core.admin.TreeTokenAccount)
      (config : zkcash_core.admin.GlobalConfig) (mb : Nat → U64) (s₁ : State) (env' : SolEnv)
      (tree' : zkcash_core.merkle_tree.MerkleTreeAccount) (ap : zkcash_core.transact.Appended),
      TransactAccountsValid d.toAddresses s tx.toTxContext a proof.input_nullifiers.val[0]!
        proof.input_nullifiers.val[1]! tree tt config ∧
      tx.minimumBalance = some mb ∧
      (s.initAccount d.programId mb a.signer a.nullifier0 nullifierAccountSpace (.nullifier 0#u8)).bind
        (·.initAccount d.programId mb a.signer a.nullifier1 nullifierAccountSpace (.nullifier 0#u8)) = some s₁ ∧
      zkcash_core.transact.transact d.crypto.hasher arkFr d.crypto.sha256 d.crypto.proofVerifier solRuntime
        { accounts := s₁, balances := s₁.balances, signer := a.signer, treeToken := a.treeTokenAccount,
          recipient := a.recipient, feeRecipient := a.feeRecipientAccount,
          rentExemptMinimum := some (mb treeTokenAccountSpace) }
        tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2 = ok (.Ok ap, env', tree') ∧
      s' = (s₁.withBalances env'.balances).set a.treeAccount
        { (s₁.withBalances env'.balances) a.treeAccount with data := .treeAccount tree' } ∧
      s'.totalLamports (txKeys a) = s.totalLamports (txKeys a) := by
  unfold execTransact at h
  split at h
  swap; · simp at h
  rename_i tree tt config htree htt hconfig
  split at h
  · simp at h
  rename_i mb hmb
  split at h
  · simp at h
  rename_i s₁ hs₁
  dsimp only at h
  split at h
  · simp at h
  rename_i hvalid
  obtain ⟨⟨r, env', tree'⟩, hres, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases r with
  | Err e => cases h
  | Ok ap =>
  obtain ⟨s₄, hbal, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases h
  obtain ⟨e1, e2⟩ := checkBalanced_spec hbal
  refine ⟨tree, tt, config, mb, s₁, env', tree', ap, not_not.mp hvalid, hmb, hs₁, ofResult_ok hres, e1, ?_⟩
  rw [e1]; exact e2

/-- Every balance of a mapped world fits a `u64`. -/
theorem toWorld_fit (d : Deployment) (rent : Nat → U64) (s : State) (x : Spec.Pubkey) :
    (toWorld d rent s).balances x < 2 ^ 64 :=
  show (s (fromPubkey x)).lamports.val < 2 ^ 64 from (s (fromPubkey x)).lamports.hBounds

/-- **The spec's rent step is Anchor's two `init`s.** With a positive rent, the signer pays each
    new nullifier address what it is missing, as the spec says (`nullifierRentEffects`). -/
theorem rentEffects_of_inits
    {d : Deployment} {rent : Nat → U64} {s s₁ : State} {signers : List Pubkey}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8}
    (hnf0 : a.nullifier0 = d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!))
    (hnf1 : a.nullifier1 = d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!))
    (hs0 : a.signer ≠ a.nullifier0) (hs1 : a.signer ≠ a.nullifier1)
    (h01 : a.nullifier0 ≠ a.nullifier1) (hnr : 0 < (rent nullifierAccountSpace).val)
    (hinits : (s.initAccount d.programId rent a.signer a.nullifier0 nullifierAccountSpace (.nullifier 0#u8)).bind
      (·.initAccount d.programId rent a.signer a.nullifier1 nullifierAccountSpace (.nullifier 0#u8)) = some s₁) :
    (Spec.nullifierRentEffects (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩) (toWorld d rent s)).balances
      = fun x => (s₁ (fromPubkey x)).lamports.val := by
  set inputs := toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩
  set W := toWorld d rent s
  obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hinits
  obtain ⟨top0, -, -, -, hex0, hlamA, -, -, -⟩ := initAccount_spec hs0 hA1
  obtain ⟨top1, -, -, -, hex1, hlam1, -, -, -⟩ := initAccount_spec hs1 hA2
  have hzA : (sA a.nullifier1).lamports.val = (s a.nullifier1).lamports.val := by
    have := congrFun hlamA a.nullifier1
    rw [moveN_other _ _ (Ne.symm hs1) (Ne.symm h01)] at this; exact this
  obtain ⟨ha0, ha1⟩ := newNullifierAccount_toWorld d rent s signers a proof ext fee out1 out2
  rw [← hnf0] at ha0; rw [← hnf1] at ha1
  have hW₁bal : W.balances = fun x => (s (fromPubkey x)).lamports.val := rfl
  have hnrW : W.nullifierRent = (rent nullifierAccountSpace).val := rfl
  have htop0' : top0 = (rent nullifierAccountSpace).val - (s a.nullifier0).lamports.val := hex0 hnr
  have htop1' : top1 = (rent nullifierAccountSpace).val - (s a.nullifier1).lamports.val := by
    rw [hex1 hnr, hzA]
  have hTop0 : W.nullifierTopUp inputs 0 = top0 := by
    unfold Spec.World.nullifierTopUp; rw [ha0, hnrW, hW₁bal]
    simp only [fromPubkey_toPubkey]; exact htop0'.symm
  show Spec.moveLamports (Spec.moveLamports W.balances inputs.s
      (W.state.newNullifierAccount inputs 0) (W.nullifierTopUp inputs 0)) inputs.s
      (W.state.newNullifierAccount inputs 1)
      (W.nullifierRent - Spec.moveLamports W.balances inputs.s
        (W.state.newNullifierAccount inputs 0) (W.nullifierTopUp inputs 0)
        (W.state.newNullifierAccount inputs 1)) = _
  have e0 := moveLamports_fromPubkey (fun k => (s k).lamports.val) a.signer a.nullifier0 top0
  beta_reduce at e0
  rw [ha0, ha1, hTop0, hW₁bal, show inputs.s = toPubkey a.signer from rfl, e0]
  simp only [fromPubkey_toPubkey]
  rw [moveN_other _ _ (Ne.symm hs1) (Ne.symm h01), hnrW, ← htop1', moveLamports_fromPubkey]
  funext x
  have := congrFun (show (fun k => (s₁ k).lamports.val) = _ by rw [hlam1, hlamA]) (fromPubkey x)
  exact this.symm

variable [Spec.PoseidonHashes] [Spec.Sha] [Spec.Groups]
  [AddCommGroup Spec.G1] [Module Spec.F Spec.G1]
  [CommGroup Spec.GT] [Spec.Pairing] [Spec.Deployment]

/-- What `transact_refines_of` needs about the signer: it is none of the program's accounts (the
    pool, the tree's and the config's account, an existing nullifier account) and neither of the
    two new nullifier accounts. From `PdasDoNotSign` (`signerNotProgram_of_pdas`), or from the
    spec's `signerNotPoolNotNullifiers` (completeness). -/
structure SignerNotProgram (d : Deployment) (s : State) (a : TransactAccounts) : Prop where
  pool : a.signer ≠ d.poolAddress
  tree : a.signer ≠ d.treeAddress
  config : a.signer ≠ d.configAddress
  nf0 : a.signer ≠ a.nullifier0
  nf1 : a.signer ≠ a.nullifier1
  nullifier : ¬ d.IsNullifierAccount s a.signer

/-- **One `transact`, exactly**, given what it needs about the signer: the spec's `transact`
    holds between the old and new worlds. (That the new state is well-formed is `wf_transact`,
    `Proofs/WellFormed.lean`.) -/
theorem transact_refines_of
    {d : Deployment} {rent : Nat → U64} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d)
    (wf : WellFormed d s)
    (hsig : SignerNotProgram d s a) (hrentPos : tx.RentPositive)
    (crypto : NewNullifierAddressesDiffer d proof) (circuit : CircuitFacts d {proof})
    (rentFixed : SameRent rent tx.minimumBalance)
    (hProofValid : d.crypto.proofVerifier.verify proof = ok true →
      Spec.proofValid (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩))
    (hmint : Spec.Deployment.solMint = toPubkey zkcash_core.transact.SOL_ADDRESS) :
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩
    Spec.transact inputs (toWorld d rent s) (toWorld d rent s') := by
  intro inputs
  have hx : execTransact d s tx a proof extAmount fee out1 out2 = .ok (s', events) := hstep
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, hvalid, hmb, hs₁, hhandler, hs', hcons⟩ := execTransact_ok hx
  have rentFixed : tx.minimumBalance = some rent := rentFixed
  have hmbr : rent = mb := by rw [rentFixed] at hmb; exact Option.some.inj hmb
  subst hmbr
  -- the program's accounts are the canonical ones
  obtain ⟨htreeAddr, hshape, -⟩ := wf.tree _ _ hvalid.treeAccount.1
  have hpoolAddr := (wf.pool _ _ hvalid.treeTokenAccount.1).1
  obtain ⟨hcfgAddr, hdr, hwr, hmr, -⟩ := wf.config _ _ hvalid.globalConfig.1
  -- the nullifier accounts
  set n0 := proof.input_nullifiers.val[0]! with hn0
  set n1 := proof.input_nullifiers.val[1]! with hn1
  have hnf0 : a.nullifier0 = d.pda (nullifier0Seeds n0) := hvalid.nullifier0.1
  have hnf1 : a.nullifier1 = d.pda (nullifier1Seeds n1) := hvalid.nullifier1.1
  have hnf01 : a.nullifier0 ≠ a.nullifier1 := by
    rw [hnf0, hnf1]; exact ne_of_distinct crypto (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl)
      (nullifier0Seeds_ne_nullifier1Seeds _ _ _ _)
  have hnr : 0 < (rent nullifierAccountSpace).val := hrentPos rent rentFixed _
  set nr := (rent nullifierAccountSpace).val with hnrdef
  -- the two `init`s: the signer tops each nullifier address up (by `top0`, `top1`)
  obtain ⟨sA, hA1, hA2⟩ := Option.bind_eq_some_iff.mp hs₁
  -- the signer is not a nullifier account: a PDA does not sign
  have hs_nf0 : a.signer ≠ a.nullifier0 := hsig.nf0
  have hs_nf1 : a.signer ≠ a.nullifier1 := hsig.nf1
  obtain ⟨top0, htop0, hsys0, hfull0, hex0, hlamA, hownA, hdataA, hotherA⟩ := initAccount_spec hs_nf0 hA1
  obtain ⟨top1, htop1, hsys1, hfull1, hex1, hlam1, hown1, hdata1, hother1⟩ := initAccount_spec hs_nf1 hA2
  have hsA : (sA a.signer).lamports.val = (s a.signer).lamports.val - top0 := by
    have := congrFun hlamA a.signer
    simp only [moveN, Function.update_of_ne hs_nf0, Function.update_self] at this; exact this
  have hzA : (sA a.nullifier1).lamports.val = (s a.nullifier1).lamports.val := by
    have := congrFun hlamA a.nullifier1
    rw [moveN_other _ _ (Ne.symm hs_nf1) (Ne.symm hnf01)] at this; exact this
  -- lamports after the two inits
  have hW₁ : (fun k => (s₁ k).lamports.val)
      = moveN (moveN (fun k => (s k).lamports.val) a.signer a.nullifier0 top0) a.signer a.nullifier1 top1 := by
    rw [hlam1, hlamA]
  -- owners and data after the two inits
  have hod₁ : ∀ k, k ≠ a.nullifier0 → k ≠ a.nullifier1 → (s₁ k).owner = (s k).owner ∧ (s₁ k).data = (s k).data := by
    intro k h0 h1
    obtain ⟨o1, d1⟩ := hother1 k h1; obtain ⟨o0, d0⟩ := hotherA k h0
    exact ⟨o1.trans o0, d1.trans d0⟩
  have hnf0₁ : (s₁ a.nullifier0).owner = d.programId ∧ (s₁ a.nullifier0).data = .nullifier 0#u8 := by
    obtain ⟨o1, d1⟩ := hother1 _ hnf01; exact ⟨o1.trans hownA, d1.trans hdataA⟩
  have hnf1₁ : (s₁ a.nullifier1).owner = d.programId ∧ (s₁ a.nullifier1).data = .nullifier 0#u8 :=
    ⟨hown1, hdata1⟩
  -- the handler
  have hok := handler_ok d.crypto d.crypto.sha256 _ tree config proof extAmount fee a.recipient a.feeRecipientAccount out1 out2
    ap env' tree' hhandler
  -- the verifier: canonical public inputs
  have hcan := verifyProof_canonical _ proof _ hok.verify
  have hcanR : Canonical proof.root := by simpa [publicInputs] using hcan 0 (by decide)
  have hcan0 : Canonical n0 := by simpa [publicInputs, hn0] using hcan 3 (by decide)
  have hcan1 : Canonical n1 := by simpa [publicInputs, hn1] using hcan 4 (by decide)
  -- what the old world reads
  have htreeAt : s.treeAccount d.treeAddress = tree := by
    simp only [PrivacyCash.Model.State.treeAccount, ← htreeAddr, hvalid.treeAccount.1.2]
  have hcfgAt : s.configAccount d.configAddress = config := by
    simp only [PrivacyCash.Model.State.configAccount, ← hcfgAddr, hvalid.globalConfig.1.2]
  have hpoolData : (s a.treeTokenAccount).data = .treeToken tt := hvalid.treeTokenAccount.1.2
  have hpoolOwner : (s a.treeTokenAccount).owner = d.programId := hvalid.treeTokenAccount.1.1
  have hsigNotPool : a.signer ≠ a.treeTokenAccount := by rw [hpoolAddr]; exact hsig.pool
  have hnf0Init : Initializable s a.nullifier0 := hvalid.nullifier0.2
  have hnf1Init : Initializable s a.nullifier1 := hvalid.nullifier1.2
  have hpool_nf0 : a.treeTokenAccount ≠ a.nullifier0 := fun e => wf.programNotSystem (by
    rw [← hpoolOwner, e]; exact hnf0Init.1)
  have hpool_nf1 : a.treeTokenAccount ≠ a.nullifier1 := fun e => wf.programNotSystem (by
    rw [← hpoolOwner, e]; exact hnf1Init.1)
  have hW₁pool₁ : (s₁ a.treeTokenAccount).lamports.val = (s a.treeTokenAccount).lamports.val := by
    rw [show (s₁ a.treeTokenAccount).lamports.val = _ from congrFun hW₁ a.treeTokenAccount,
      moveN_other _ _ (Ne.symm hsigNotPool) hpool_nf1, moveN_other _ _ (Ne.symm hsigNotPool) hpool_nf0]
  have hW₁sig : (s₁ a.signer).lamports.val = (s a.signer).lamports.val - top0 - top1 := by
    rw [show (s₁ a.signer).lamports.val = _ from congrFun hW₁ a.signer]
    simp only [moveN, Function.update_of_ne hs_nf1, Function.update_of_ne hs_nf0, Function.update_self]
  obtain ⟨v, hv, hdep, hwd, hdepFit⟩ := hok.rent
  have hvr : v = rent treeTokenAccountSpace := (Option.some.inj hv).symm
  subst hvr
  have hpub0 : Spec.pubAmtConsistent extAmount.val fee.val (toF proof.public_amount) ∧
      Spec.amountsInRange extAmount.val fee.val ∧ extAmount.val ≠ 0 := by
    have := (checkPublicAmount_eq extAmount fee proof.public_amount).symm.trans hok.pubAmt
    simpa using this
  have hpub := hpub0.1
  have hext0 : extAmount.val ≠ 0 := hpub0.2.2
  -- the new state, account by account
  have hs'k : ∀ k, (s' k).lamports = env'.balances k ∧ (s' k).owner = (s₁ k).owner ∧
      (s' k).data = (if k = a.treeAccount then .treeAccount tree' else (s₁ k).data) := by
    intro k; rw [hs']
    by_cases hk : k = a.treeAccount
    · subst hk; simp [State.set, State.withBalances]
    · simp [State.set, hk, State.withBalances]
  -- lamport conservation (the runtime's check) rules out paying the pool from itself
  have mS : a.signer ∈ txKeys a := by simp [txKeys]
  have m0 : a.nullifier0 ∈ txKeys a := by simp [txKeys]
  have m1 : a.nullifier1 ∈ txKeys a := by simp [txKeys]
  have mP : a.treeTokenAccount ∈ txKeys a := by simp [txKeys]
  have mA : a.recipient ∈ txKeys a := by simp [txKeys]
  have mT : a.feeRecipientAccount ∈ txKeys a := by simp [txKeys]
  have hTLend : TL (txKeys a) (fun k => (env'.balances k).val)
      = TL (txKeys a) (fun k => (s k).lamports.val) := by
    have e1 : (fun k => (env'.balances k).val) = fun k => (s' k).lamports.val := by
      funext k; rw [(hs'k k).1]
    rw [e1, ← totalLamports_eq, ← totalLamports_eq, hcons]
  have hTL₁ : TL (txKeys a) (fun k => (s k).lamports.val) ≤ TL (txKeys a) (fun k => (s₁ k).lamports.val) := by
    rw [hW₁]; exact le_trans (TL_moveN_ge mS m0 _ _) (TL_moveN_ge mS m1 _ _)
  have hnoself : (extAmount.val < 0 → a.recipient ≠ a.treeTokenAccount) ∧
      (fee.val > 0 → a.feeRecipientAccount ≠ a.treeTokenAccount) := by
    have hfin : TL (txKeys a) (fun k => (s₁ k).lamports.val)
        + (if extAmount.val < 0 ∧ a.recipient = a.treeTokenAccount then (extAmount.val.natAbs : ℤ) else 0)
        + (if a.feeRecipientAccount = a.treeTokenAccount then (fee.val : ℤ) else 0)
        ≤ TL (txKeys a) (fun k => (env'.balances k).val) := by
      by_cases hp : extAmount.val > 0
      · have he : (fun k => (env'.balances k).val) = payN (moveN (fun k => (s₁ k).lamports.val)
            a.signer a.treeTokenAccount extAmount.val.natAbs) a.treeTokenAccount a.feeRecipientAccount
            fee.val := (hdep hp).2.2.2.2
        rw [he, if_neg (fun h => by omega)]
        have h1 := TL_moveN_ge mS mP (fun k => (s₁ k).lamports.val) extAmount.val.natAbs
        have h2 := TL_payN_ge mP mT (moveN (fun k => (s₁ k).lamports.val) a.signer a.treeTokenAccount
          extAmount.val.natAbs) fee.val
        omega
      · have hn : extAmount.val < 0 := by omega
        have he : (fun k => (env'.balances k).val) = payN (payN (fun k => (s₁ k).lamports.val)
            a.treeTokenAccount a.recipient extAmount.val.natAbs) a.treeTokenAccount a.feeRecipientAccount
            fee.val := (hwd hn).2
        rw [he]
        have h1 := TL_payN_ge mP mA (fun k => (s₁ k).lamports.val) extAmount.val.natAbs
        have h2 := TL_payN_ge mP mT (payN (fun k => (s₁ k).lamports.val) a.treeTokenAccount a.recipient
          extAmount.val.natAbs) fee.val
        by_cases hA : a.recipient = a.treeTokenAccount
        · rw [if_pos ⟨hn, hA⟩]; rw [if_pos hA] at h1; omega
        · rw [if_neg (fun h => hA h.2)]; rw [if_neg hA] at h1; omega
    rw [hTLend] at hfin
    have hA0 : (0 : ℤ) ≤ (if extAmount.val < 0 ∧ a.recipient = a.treeTokenAccount
        then (extAmount.val.natAbs : ℤ) else 0) := by split <;> omega
    have hT0 : (0 : ℤ) ≤ (if a.feeRecipientAccount = a.treeTokenAccount then (fee.val : ℤ) else 0) := by
      split <;> omega
    refine ⟨fun hn hA => ?_, fun hf hT => ?_⟩
    · rw [if_pos ⟨hn, hA⟩] at hfin hA0
      have : (0 : ℤ) < (extAmount.val.natAbs : ℤ) := by exact_mod_cast Int.natAbs_pos.mpr (by omega)
      omega
    · rw [if_pos hT] at hfin hT0
      have : (0 : ℤ) < (fee.val : ℤ) := by exact_mod_cast hf
      omega
  have hfeeOk : a.feeRecipientAccount ≠ a.treeTokenAccount ∨ fee.val = 0 := by
    by_cases hf : fee.val > 0
    · exact Or.inl (hnoself.2 hf)
    · exact Or.inr (by omega)
  -- the two appends
  obtain ⟨p1, p2, t1, hap1, hap2⟩ := hok.appends
  -- the leaves are public inputs 5 and 6 (range-checked), the subtrees are canonical (`WellFormed`)
  have hl0 : Canonical proof.output_commitments.val[0]! := by simpa [publicInputs] using hcan 5 (by decide)
  have hl1 : Canonical proof.output_commitments.val[1]! := by simpa [publicInputs] using hcan 6 (by decide)
  have hsub0 := wf.storedSubtrees _ _ hvalid.treeAccount.1
  obtain ⟨hT1, hsh1, hroom1, hidx1, hau1, hmax1, -⟩ := append_ok' d hashes _ tree t1 p1 hshape hsub0 hl0 hap1
  have hsub1 := append_subtrees_canonical' d hashes _ tree t1 p1 hshape hsub0 hl0 hap1
  obtain ⟨hT2, hsh2, hroom2, -, hau2, hmax2, -⟩ := append_ok' d hashes _ t1 tree' p2 hsh1 hsub1 hl1 hap2
  -- external data
  obtain ⟨hsh, hcalc, hEq⟩ := hok.extHash
  -- the code returned a hash, so the serialized data fit in a vector
  have hvecFit := extDataHash_ok_fits hcalc
  have hcalc' := (extDataHash_eq d.crypto.sha256 a.recipient a.feeRecipientAccount
    zkcash_core.transact.SOL_ADDRESS extAmount out1 out2 fee inputs rfl rfl rfl rfl rfl rfl rfl
    hvecFit).symm.trans hcalc
  have hfits : Spec.encOutsFit inputs := by
    by_contra hn; rw [if_neg hn] at hcalc'; have := Result.ok_injective hcalc'; simp at this
  rw [if_pos hfits] at hcalc'
  obtain ⟨hsh', hsha, hcalc'⟩ := bindOk hcalc'
  have hshe : hsh' = hsh := Option.some.inj (Result.ok_injective hcalc')
  subst hshe
  have hser : Spec.externalDataHash inputs = inputs.extDataHash := by
    have hb := hashes.sha256_ok hsha
    have hlen : (Spec.serealizeExternalData inputs).length ≤ Usize.max := by
      rw [serLength]
      have : inputs.encOut0.length + inputs.encOut1.length = out1.length + out2.length := by
        simp [inputs, toInputs, toBytes, Slice.length]
      have := hvecFit; omega
    rw [toBytes_toSlice _ hlen] at hb
    simp only [Spec.externalDataHash, ← hb, natOfLE_toBytes]
    rw [show inputs.extDataHash = toF proof.ext_data_hash from rfl, toF_def]
    exact hEq
  have hpoolDataN : ∀ b, (s a.treeTokenAccount).data ≠ .nullifier b := by
    rw [hpoolData]; intro b h; cases h
  have hbounds := i64_bounds extAmount
  have hfeeb : fee.val < 2 ^ 64 := by scalar_tac
  have htree_nf0 : a.treeAccount ≠ a.nullifier0 := fun e => wf.programNotSystem (by
    rw [← hvalid.treeAccount.1.1, e]; exact hnf0Init.1)
  have htree_nf1 : a.treeAccount ≠ a.nullifier1 := fun e => wf.programNotSystem (by
    rw [← hvalid.treeAccount.1.1, e]; exact hnf1Init.1)
  have hcfgOwner : (s a.globalConfig).owner = d.programId := hvalid.globalConfig.1.1
  have hcfg_nf0 : a.globalConfig ≠ a.nullifier0 := fun e => wf.programNotSystem (by
    rw [← hcfgOwner, e]; exact hnf0Init.1)
  have hcfg_nf1 : a.globalConfig ≠ a.nullifier1 := fun e => wf.programNotSystem (by
    rw [← hcfgOwner, e]; exact hnf1Init.1)
  have hcfg_tree : a.globalConfig ≠ a.treeAccount := fun e => by
    have h1 := hvalid.globalConfig.1.2; have h2 := hvalid.treeAccount.1.2
    rw [e, h2] at h1; cases h1
  have htreeAt' : s'.treeAccount d.treeAddress = tree' := by
    simp only [PrivacyCash.Model.State.treeAccount, ← htreeAddr, (hs'k a.treeAccount).2.2, if_true]
  have hcfgAt' : s'.configAccount d.configAddress = config := by
    simp only [PrivacyCash.Model.State.configAccount, ← hcfgAddr, (hs'k a.globalConfig).2.2, if_neg hcfg_tree,
      (hod₁ _ hcfg_nf0 hcfg_nf1).2, hvalid.globalConfig.1.2]
  -- the code's balances after the handler
  set Teff : (Pubkey → ℕ) → (Pubkey → ℕ) := fun B =>
    if extAmount.val > 0 then moveN B a.signer a.treeTokenAccount extAmount.val.natAbs
    else moveN B a.treeTokenAccount a.recipient extAmount.val.natAbs with hTdef
  have hcode : (fun k => (env'.balances k).val)
      = moveN (Teff (fun k => (s₁ k).lamports.val)) a.treeTokenAccount a.feeRecipientAccount fee.val := by
    by_cases hp : extAmount.val > 0
    · have he : (fun k => (env'.balances k).val) = payN (moveN (fun k => (s₁ k).lamports.val)
          a.signer a.treeTokenAccount extAmount.val.natAbs) a.treeTokenAccount a.feeRecipientAccount
          fee.val := (hdep hp).2.2.2.2
      rw [he, payN_eq_moveN _ _ _ _ hfeeOk]; simp only [hTdef, if_pos hp]
    · have hn : extAmount.val < 0 := by omega
      have he : (fun k => (env'.balances k).val) = payN (payN (fun k => (s₁ k).lamports.val)
          a.treeTokenAccount a.recipient extAmount.val.natAbs) a.treeTokenAccount a.feeRecipientAccount
          fee.val := (hwd hn).2
      rw [he, payN_eq_moveN _ _ _ _ hfeeOk, payN_eq_moveN _ _ _ _ (Or.inl (hnoself.1 hn))]
      simp only [hTdef, if_neg hp]
  -- THE SPEC WORLD BEFORE: every account's lamports
  set W₁ := toWorld d rent s with hW₁def
  have hW₁bal : W₁.balances = fun x => (s (fromPubkey x)).lamports.val := rfl
  have hnrW : W₁.nullifierRent = nr := rfl
  have hbalPool : W₁.poolBalance = (s a.treeTokenAccount).lamports.val := by
    show (s (fromPubkey (toPubkey d.poolAddress))).lamports.val = _
    rw [fromPubkey_toPubkey, ← hpoolAddr]
  have hW₁pool : W₁.state.pool = toPubkey a.treeTokenAccount := by
    show toPubkey d.poolAddress = _; rw [hpoolAddr]
  -- the addresses of the new nullifier accounts
  obtain ⟨hb00, hb01⟩ := nullifierAddrOf_bytes d n0
  obtain ⟨hb10, hb11⟩ := nullifierAddrOf_bytes d n1
  have hby0 : inputs.nullifierBytes 0 = toBytes n0.val := by
    simp [inputs, toInputs, Spec.TxInputs.nullifierBytes, publicInputs, hn0]
  have hby1 : inputs.nullifierBytes 1 = toBytes n1.val := by
    simp [inputs, toInputs, Spec.TxInputs.nullifierBytes, publicInputs, hn1]
  have ha0 : W₁.state.newNullifierAccount inputs 0 = toPubkey a.nullifier0 := by
    show nullifierAddrOf d 0 (inputs.nullifierBytes 0) = _; rw [hby0, hb00, hnf0]
  have ha1 : W₁.state.newNullifierAccount inputs 1 = toPubkey a.nullifier1 := by
    show nullifierAddrOf d 1 (inputs.nullifierBytes 1) = _; rw [hby1, hb11, hnf1]
  -- the top-ups are the code's
  have htop0' : top0 = nr - (s a.nullifier0).lamports.val := hex0 hnr
  have htop1' : top1 = nr - (s a.nullifier1).lamports.val := by rw [hex1 hnr, hzA]
  have hTop0 : W₁.nullifierTopUp inputs 0 = top0 := by
    unfold Spec.World.nullifierTopUp; rw [ha0, hnrW, hW₁bal]
    simp only [fromPubkey_toPubkey]; exact htop0'.symm
  have hTop1 : W₁.nullifierTopUp inputs 1 = top1 := by
    unfold Spec.World.nullifierTopUp; rw [ha1, hnrW, hW₁bal]
    simp only [fromPubkey_toPubkey]; exact htop1'.symm
  -- the rent step is the two `init`s
  have hrentEff : (Spec.nullifierRentEffects inputs W₁).balances
      = fun x => (s₁ (fromPubkey x)).lamports.val := by
    show Spec.moveLamports (Spec.moveLamports W₁.balances inputs.s
        (W₁.state.newNullifierAccount inputs 0) (W₁.nullifierTopUp inputs 0)) inputs.s
        (W₁.state.newNullifierAccount inputs 1)
        (W₁.nullifierRent - Spec.moveLamports W₁.balances inputs.s
          (W₁.state.newNullifierAccount inputs 0) (W₁.nullifierTopUp inputs 0)
          (W₁.state.newNullifierAccount inputs 1)) = _
    have e0 := moveLamports_fromPubkey (fun k => (s k).lamports.val) a.signer a.nullifier0 top0
    beta_reduce at e0
    rw [ha0, ha1, hTop0, hW₁bal, show inputs.s = toPubkey a.signer from rfl, e0]
    simp only [fromPubkey_toPubkey]
    rw [moveN_other _ _ (Ne.symm hs_nf1) (Ne.symm hnf01), hnrW, ← htop1', moveLamports_fromPubkey]
    funext x
    exact (congrFun hW₁ _).symm
  have hR : Spec.nullifierRentEffects inputs W₁
      = { W₁ with balances := fun x => (s₁ (fromPubkey x)).lamports.val } := by
    rw [← hrentEff]; rfl
  -- BALANCES: the spec's effects are the code's
  have hspecBal : (Spec.transactEffects inputs W₁).balances
      = fun x => (env'.balances (fromPubkey x)).val := by
    have hext' : inputs.extAmt ≠ 0 := hext0
    simp only [Spec.transactEffects]
    rw [hR]
    simp only [Spec.transferEffects, if_neg hext', hW₁pool]
    have hs : inputs.s = toPubkey a.signer := rfl
    have hA : inputs.A = toPubkey a.recipient := rfl
    have ht : inputs.t = toPubkey a.feeRecipientAccount := rfl
    have hf : inputs.f = fee.val := rfl
    have he : inputs.extAmt = extAmount.val := rfl
    rw [hs, hA, ht, hf, he]
    funext x
    rw [show (env'.balances (fromPubkey x)).val
      = (fun k => (env'.balances k).val) (fromPubkey x) from rfl, hcode]
    simp only [hTdef]
    split
    · have e1 := moveLamports_fromPubkey (fun k => (s₁ k).lamports.val) a.signer a.treeTokenAccount
        extAmount.val.natAbs
      beta_reduce at e1
      rw [e1, moveLamports_fromPubkey]
    · have e1 := moveLamports_fromPubkey (fun k => (s₁ k).lamports.val) a.treeTokenAccount a.recipient
        extAmount.val.natAbs
      beta_reduce at e1
      rw [e1, moveLamports_fromPubkey]
  -- the preconditions
  have hPS : Spec.poolSolvent W₁.poolBalance W₁.rentExemptMin inputs.extAmt inputs.f := by
    rw [hbalPool]
    refine ⟨fun hn => ?_, fun ⟨hp, hf⟩ => ?_⟩
    · obtain ⟨hpoolv, -⟩ := hwd hn
      have h2 : (s₁ a.treeTokenAccount).lamports.val ≥ extAmount.val.natAbs + fee.val + (rent treeTokenAccountSpace).val := hpoolv
      rw [hW₁pool₁] at h2
      have h1 : ((extAmount.val.natAbs : ℕ) : ℤ) = |extAmount.val| := Int.natCast_natAbs _
      show ((s a.treeTokenAccount).lamports.val : ℤ) ≥ |extAmount.val| + (fee.val : ℤ) + ((rent treeTokenAccountSpace).val : ℤ)
      omega
    · have hp' : extAmount.val ≥ 0 := hp
      have hpos : extAmount.val > 0 := by omega
      have hfv : fee.val > 0 := by exact_mod_cast hf
      have hm : moveN (fun k => (s₁ k).lamports.val) a.signer a.treeTokenAccount extAmount.val.natAbs
          a.treeTokenAccount ≥ fee.val + (rent treeTokenAccountSpace).val := (hdep hpos).2.2.2.1 hfv
      have e : moveN (fun k => (s₁ k).lamports.val) a.signer a.treeTokenAccount extAmount.val.natAbs
          a.treeTokenAccount = (s₁ a.treeTokenAccount).lamports.val + extAmount.val.natAbs := by
        simp only [moveN, Function.update_self, Function.update_of_ne (Ne.symm hsigNotPool)]
      rw [e, hW₁pool₁] at hm
      have hab : ((extAmount.val.natAbs : ℕ) : ℤ) = extAmount.val := Int.natAbs_of_nonneg (le_of_lt hpos)
      show ((s a.treeTokenAccount).lamports.val : ℤ) + extAmount.val ≥ (fee.val : ℤ) + ((rent treeTokenAccountSpace).val : ℤ)
      omega
  have hSS : Spec.signerSolvent W₁.balances inputs.s inputs.extAmt
      (W₁.nullifierTopUp inputs 0 + W₁.nullifierTopUp inputs 1) := by
    rw [hTop0, hTop1]
    show (s (fromPubkey (toPubkey a.signer))).lamports.val ≥ top0 + top1 + _
    rw [fromPubkey_toPubkey]
    have h1 := htop1; rw [hsA] at h1
    split
    · rename_i hp
      obtain ⟨-, -, hle, -, -⟩ := hdep hp
      have hle' : extAmount.val ≤ (((s₁ a.signer).lamports.val : ℕ) : ℤ) := hle
      have hp' : extAmount.val > 0 := hp
      rw [hW₁sig] at hle'
      show (s a.signer).lamports.val ≥ top0 + top1 + extAmount.val.natAbs
      omega
    · omega
  have hSep : Spec.poolNotRecipient inputs W₁.state.pool := by
    rw [hW₁pool]
    exact ⟨fun hn e => hnoself.1 hn (toPubkey_inj e), fun hf e => hnoself.2 hf (toPubkey_inj e)⟩
  -- the signer is none of the program's accounts
  have hPda : Spec.signerNotPoolNotNullifiers inputs W₁.state := by
    refine ⟨?_, ?_, ?_⟩
    · rintro (e | e | e | e)
      · rw [hW₁pool] at e; exact hsigNotPool (toPubkey_inj e)
      · have e' : toPubkey a.signer ∈ nullifierAccountsOf d s := e
        obtain ⟨ho, b, hd⟩ := mem_nullifierAccountsOf.mp e'
        rw [fromPubkey_toPubkey] at ho hd
        exact hsig.nullifier ⟨ho, b, hd⟩
      · exact hsig.tree (toPubkey_inj e)
      · exact hsig.config (toPubkey_inj e)
    · rw [ha0]; exact fun e => hs_nf0 (toPubkey_inj e)
    · rw [ha1]; exact fun e => hs_nf1 (toPubkey_inj e)
  -- a new nullifier account is system-owned, the tree's and the config's accounts are the program's
  have hTreeOwn : (s d.treeAddress).owner = d.programId := by
    rw [← htreeAddr]; exact hvalid.treeAccount.1.1
  have hCfgOwn : (s d.configAddress).owner = d.programId := by
    rw [← hcfgAddr]; exact hvalid.globalConfig.1.1
  have hNew : Spec.nullifierAccountsCreatable W₁.state inputs := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ha0, ha1]; exact fun e => hnf01 (toPubkey_inj e)
    · rw [ha0]; rintro (e | e | e | e)
      · rw [hW₁pool] at e; exact hpool_nf0 (toPubkey_inj e).symm
      · exact not_nullifierAccount_of_system wf.programNotSystem hnf0Init.1 e
      · exact wf.programNotSystem (by rw [← hTreeOwn, ← toPubkey_inj e]; exact hnf0Init.1)
      · exact wf.programNotSystem (by rw [← hCfgOwn, ← toPubkey_inj e]; exact hnf0Init.1)
    · rw [ha1]; rintro (e | e | e | e)
      · rw [hW₁pool] at e; exact hpool_nf1 (toPubkey_inj e).symm
      · exact not_nullifierAccount_of_system wf.programNotSystem hnf1Init.1 e
      · exact wf.programNotSystem (by rw [← hTreeOwn, ← toPubkey_inj e]; exact hnf1Init.1)
      · exact wf.programNotSystem (by rw [← hCfgOwn, ← toPubkey_inj e]; exact hnf1Init.1)
  have hpre : Spec.transactPreconditions inputs W₁ := by
    refine ⟨?knownRoot, hser, ?minimumFee, hpub, hProofValid hok.verify, ?fresh, ?distinct,
      hNew, ?depositLimit, hPS, hSS, List.mem_map_of_mem hvalid.signer, hPda, ?room, ?range, hfits,
      hSep, ?canonical, ?fit, hmint.symm⟩
    case knownRoot =>
      show Spec.rootBytesKnown (toTree (s.treeAccount d.treeAddress)) (toBytes proof.root.val)
      rw [htreeAt, rootBytesKnown_iff]
      exact ⟨hcanR, isKnownRoot_safe tree proof.root hshape hcanR hok.root⟩
    case canonical =>
      intro i
      show Spec.canonicalEncoding (toBytes ((publicInputs proof)[i.val]!).val)
        (Spec.Groth16.toVector inputs.pubInputs i)
      rw [canonicalEncoding_iff]
      exact ⟨hcan i.val i.isLt, by fin_cases i <;> rfl⟩
    case minimumFee =>
      show Spec.feeSufficient (toConfig (s.configAccount d.configAddress) (s.treeAccount d.treeAddress)) _ _
      rw [hcfgAt, htreeAt]
      exact ((validateFee_iff extAmount fee config tree hdr hwr hmr).mp hok.feeOk).2
    case fresh =>
      have hns := wf.programNotSystem
      show ¬ (nullifierAddrOf d 0 (inputs.nullifierBytes 0) ∈ nullifierAccountsOf d s ∨
          nullifierAddrOf d 1 (inputs.nullifierBytes 0) ∈ nullifierAccountsOf d s) ∧
        ¬ (nullifierAddrOf d 0 (inputs.nullifierBytes 1) ∈ nullifierAccountsOf d s ∨
          nullifierAddrOf d 1 (inputs.nullifierBytes 1) ∈ nullifierAccountsOf d s)
      rw [hby0, hby1, hb00, hb01, hb10, hb11, ← hnf0, ← hnf1, ← hvalid.nullifier2.1,
        ← hvalid.nullifier3.1]
      exact ⟨not_or.mpr ⟨not_nullifierAccount_of_system hns hnf0Init.1,
          not_nullifierAccount_of_system hns hvalid.nullifier3.2⟩,
        not_or.mpr ⟨not_nullifierAccount_of_system hns hvalid.nullifier2.2,
          not_nullifierAccount_of_system hns hnf1Init.1⟩⟩
    case distinct =>
      show toF n0 ≠ toF n1
      exact fun h => circuit.distinctNullifiers proof (Set.mem_singleton proof) hok.verify (toF_injOn hcan0 hcan1 h)
    case depositLimit =>
      show extAmount.val > 0 → extAmount.val ≤ ((toConfig (s.configAccount d.configAddress) (s.treeAccount d.treeAddress)).maxDepositLimit : ℤ)
      rw [hcfgAt, htreeAt]; intro hp
      have := hok.depositLimit hp; simpa [toConfig] using this
    case room =>
      show (toTree (s.treeAccount d.treeAddress)).nextIndex ≤ 2 ^ 26 - 2
      rw [htreeAt]; simp only [toTree]; omega
    case range =>
      exact hpub0.2.1
    case fit =>
      refine ⟨fun k _ => ?_, fun hp => ?_⟩
      · rw [← Spec.transactEffects_balances inputs _ hSS hPS hSep hPda hNew k, hspecBal]
        exact_mod_cast u64_lt (env'.balances (fromPubkey k))
      · have hp' : extAmount.val > 0 := hp
        have hm : moveN (fun k => (s₁ k).lamports.val) a.signer a.treeTokenAccount
            extAmount.val.natAbs a.treeTokenAccount < 2 ^ 64 := hdepFit hp'
        have e : moveN (fun k => (s₁ k).lamports.val) a.signer a.treeTokenAccount extAmount.val.natAbs
            a.treeTokenAccount = (s₁ a.treeTokenAccount).lamports.val + extAmount.val.natAbs := by
          simp only [moveN, Function.update_self, Function.update_of_ne (Ne.symm hsigNotPool)]
        rw [e, hW₁pool₁] at hm
        rw [hbalPool]
        have hab : ((extAmount.val.natAbs : ℕ) : ℤ) = extAmount.val := Int.natAbs_of_nonneg (le_of_lt hp')
        show ((s a.treeTokenAccount).lamports.val : ℤ) + extAmount.val < 2 ^ 64
        omega
  -- what the step keeps: accounts other than the tree and the two new nullifier accounts
  have hfromOld : ∀ k, k ≠ a.treeAccount → k ≠ a.nullifier0 → k ≠ a.nullifier1 →
      (s' k).owner = (s k).owner ∧ (s' k).data = (s k).data := by
    intro k ht h0 h1
    obtain ⟨-, ho', hd'⟩ := hs'k k
    rw [ho', hd', if_neg ht]; exact hod₁ k h0 h1
  have hnfData' : ∀ k, (k = a.nullifier0 ∨ k = a.nullifier1) → ∃ b, (s' k).data = .nullifier b := by
    rintro k (rfl | rfl)
    · exact ⟨_, by rw [(hs'k _).2.2, if_neg (Ne.symm htree_nf0), hnf0₁.2]⟩
    · exact ⟨_, by rw [(hs'k _).2.2, if_neg (Ne.symm htree_nf1), hnf1₁.2]⟩
  -- the effects
  have heff : Spec.AgreesOnProgramEffects inputs (Spec.transactEffects inputs W₁)
      (toWorld d rent s') := by
    have hext' : inputs.extAmt ≠ 0 := hext0
    refine ⟨?tree, ?nulls, ?pool, ?addr, ?config, ?treeA, ?cfgA, ?rentEx, ?nrent, ?bal⟩
    case treeA =>
      simp only [Spec.transactEffects, Spec.transferEffects, if_neg hext']; rfl
    case cfgA =>
      simp only [Spec.transactEffects, Spec.transferEffects, if_neg hext']; rfl
    case nulls =>
      show nullifierAccountsOf d s' = (Spec.transferEffects inputs
        (Spec.nullifierRentEffects inputs W₁)).state.nullifierAccounts ∪
          {W₁.state.newNullifierAccount inputs 0, W₁.state.newNullifierAccount inputs 1}
      rw [Spec.transferEffects_state, Spec.nullifierRentEffects_state, ha0, ha1]
      ext x
      rw [Finset.mem_union, mem_nullifierAccountsOf, Finset.mem_insert, Finset.mem_singleton]
      show d.IsNullifierAccount s' (fromPubkey x) ↔
        x ∈ nullifierAccountsOf d s ∨ x = toPubkey a.nullifier0 ∨ x = toPubkey a.nullifier1
      rw [mem_nullifierAccountsOf]
      have hx : x = toPubkey (fromPubkey x) := (toPubkey_fromPubkey x).symm
      set k := fromPubkey x
      constructor
      · rintro ⟨ho, b, hd⟩
        by_cases h0 : k = a.nullifier0
        · right; left; rw [hx, h0]
        by_cases h1 : k = a.nullifier1
        · right; right; rw [hx, h1]
        left
        have ht : k ≠ a.treeAccount := fun e => by
          rw [(hs'k k).2.2, if_pos e] at hd; cases hd
        obtain ⟨ho', hd'⟩ := hfromOld k ht h0 h1
        exact ⟨by rw [← ho']; exact ho, b, by rw [← hd']; exact hd⟩
      · rintro (⟨ho, b, hd⟩ | h | h)
        · have ht : k ≠ a.treeAccount := fun e => by
            rw [e, hvalid.treeAccount.1.2] at hd; cases hd
          have h0 : k ≠ a.nullifier0 := fun e => by rw [e, hnf0Init.2] at hd; cases hd
          have h1 : k ≠ a.nullifier1 := fun e => by rw [e, hnf1Init.2] at hd; cases hd
          obtain ⟨ho', hd'⟩ := hfromOld k ht h0 h1
          exact ⟨by rw [ho']; exact ho, b, by rw [hd']; exact hd⟩
        · have hk : k = a.nullifier0 := by rw [show k = fromPubkey x from rfl, h, fromPubkey_toPubkey]
          rw [hk]
          exact ⟨by rw [(hs'k _).2.1]; exact hnf0₁.1, hnfData' _ (Or.inl rfl)⟩
        · have hk : k = a.nullifier1 := by rw [show k = fromPubkey x from rfl, h, fromPubkey_toPubkey]
          rw [hk]
          exact ⟨by rw [(hs'k _).2.1]; exact hnf1₁.1, hnfData' _ (Or.inr rfl)⟩
    case addr =>
      simp only [Spec.transactEffects, Spec.transferEffects, if_neg hext']; rfl
    case rentEx =>
      simp only [Spec.transactEffects, Spec.transferEffects, if_neg hext']; rfl
    case nrent =>
      simp only [Spec.transactEffects, Spec.transferEffects, if_neg hext']; rfl
    case tree =>
      show toTree (s'.treeAccount d.treeAddress) = _
      simp only [Spec.transactEffects, Spec.transferEffects, if_neg hext']
      rw [htreeAt']
      show toTree tree' = Spec.appendEffects (toF proof.output_commitments.val[1]!)
        (Spec.appendEffects (toF proof.output_commitments.val[0]!) (toTree (s.treeAccount d.treeAddress)))
      rw [htreeAt, ← hT1, ← hT2]
    case pool =>
      simp only [Spec.transactEffects, Spec.transferEffects, if_neg hext']; rfl
    case config =>
      show toConfig (s'.configAccount d.configAddress) (s'.treeAccount d.treeAddress) = _
      simp only [Spec.transactEffects, Spec.transferEffects, if_neg hext']
      show toConfig (s'.configAccount d.configAddress) (s'.treeAccount d.treeAddress)
        = toConfig (s.configAccount d.configAddress) (s.treeAccount d.treeAddress)
      rw [hcfgAt', htreeAt', hcfgAt, htreeAt]
      simp only [toConfig, hmax2, hmax1, hau2, hau1]
    case bal =>
      rw [hspecBal]
      funext x
      show (s' (fromPubkey x)).lamports.val = _
      rw [(hs'k _).1]
  exact ⟨hpre, heff⟩

omit [Spec.PoseidonHashes] [Spec.Sha] [Spec.Groups] [AddCommGroup Spec.G1]
  [Module Spec.F Spec.G1] [CommGroup Spec.GT] [Spec.Pairing]
  [Spec.Deployment] in
/-- What `PdasDoNotSign` gives about the signer of an accepted `transact`. -/
theorem signerNotProgram_of_pdas {d : Deployment} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (wf : WellFormed d s) (solana : PdasDoNotSign d tx.toTxContext) : SignerNotProgram d s a := by
  have hx : execTransact d s tx a proof extAmount fee out1 out2 = .ok (s', events) := hstep
  obtain ⟨tree, tt, config, mb, s₁, env', tree', ap, hvalid, -⟩ := execTransact_ok hx
  have hsig : ∀ seeds, a.signer ≠ d.pda seeds := fun seeds e => solana seeds (e ▸ hvalid.signer)
  refine ⟨hsig _, hsig _, hsig _, ?_, ?_, ?_⟩
  · rw [hvalid.nullifier0.1]; exact hsig _
  · rw [hvalid.nullifier1.1]; exact hsig _
  · rintro ⟨ho, b, hd⟩
    obtain ⟨seeds, hk⟩ := wf.nullifiers _ b ⟨ho, hd⟩
    exact hsig seeds hk

/-- **One `transact`, exactly**: the spec's `transact` holds between the old and new worlds. -/
theorem transact_refines
    {d : Deployment} {rent : Nat → U64} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d)
    (wf : WellFormed d s)
    (solana : PdasDoNotSign d tx.toTxContext) (hrentPos : tx.RentPositive)
    (crypto : NewNullifierAddressesDiffer d proof) (circuit : CircuitFacts d {proof})
    (rentFixed : SameRent rent tx.minimumBalance)
    (hProofValid : d.crypto.proofVerifier.verify proof = ok true →
      Spec.proofValid (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩))
    (hmint : Spec.Deployment.solMint = toPubkey zkcash_core.transact.SOL_ADDRESS) :
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩
    Spec.transact inputs (toWorld d rent s) (toWorld d rent s') :=
  transact_refines_of hstep hashes wf (signerNotProgram_of_pdas hstep wf solana) hrentPos crypto
    circuit rentFixed hProofValid hmint

/-- **One `transact`, up to changes allowed between transactions**: the spec's `transact` holds
    from the old world after an allowed change, to a world from which an allowed change leads to
    the new world. Here both changes are none. -/
theorem transact_refines_between
    {d : Deployment} {rent : Nat → U64} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d)
    (wf : WellFormed d s)
    (solana : PdasDoNotSign d tx.toTxContext) (hrentPos : tx.RentPositive)
    (crypto : NewNullifierAddressesDiffer d proof) (circuit : CircuitFacts d {proof})
    (rentFixed : tx.minimumBalance = some rent)
    (hProofValid : d.crypto.proofVerifier.verify proof = ok true →
      Spec.proofValid (toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩))
    (hmint : Spec.Deployment.solMint = toPubkey zkcash_core.transact.SOL_ADDRESS) :
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩
    ∃ b₁ : Spec.UpdatedValuesBetweenTransacts, b₁.Allowed (toWorld d rent s) ∧
      ∃ b₂ : Spec.UpdatedValuesBetweenTransacts,
      Spec.transact inputs ((toWorld d rent s).withUpdatedValues b₁)
        ((toWorld d rent s').withUpdatedValues b₂) ∧
      (Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s')).Allowed
        ((toWorld d rent s').withUpdatedValues b₂) ∧
      b₁.adminChanges = [] ∧
      b₁.balances (toPubkey d.poolAddress) = s.lamports d.poolAddress ∧
      b₂.config = (toWorld d rent s').state.config ∧
      b₂.balances (toPubkey d.poolAddress) = s'.lamports d.poolAddress := by
  have htx :=
    transact_refines hstep hashes wf solana hrentPos crypto circuit rentFixed hProofValid hmint
  have h1 := Spec.World.withUpdatedValues_self (toWorld d rent s)
  have h2 := Spec.World.withUpdatedValues_self (toWorld d rent s')
  refine ⟨Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s),
    Spec.UpdatedValuesBetweenTransacts.Allowed.self _ (toWorld_fit d rent s),
    Spec.UpdatedValuesBetweenTransacts.unchanged (toWorld d rent s'),
    by rw [h1, h2]; exact htx, by rw [h2]; exact .self _ (toWorld_fit d rent s'), rfl, ?_, rfl, ?_⟩
  · show s.lamports (fromPubkey (toPubkey d.poolAddress)) = _; rw [fromPubkey_toPubkey]
  · show s'.lamports (fromPubkey (toPubkey d.poolAddress)) = _; rw [fromPubkey_toPubkey]

end Connection
