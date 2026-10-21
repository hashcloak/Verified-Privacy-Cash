import Connection.Proofs.Checks
import Connection.Proofs.ExtData
import Connection.Proofs.Tree
import Connection.Proofs.Verifier
import Connection.Proofs.Transact
import Connection.Proofs.Bridge
import Connection.Proofs.WellFormed
import Connection.Proofs.HandlerComplete
import Connection.Proofs.ToyRun
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Connection theorems

REVIEW SURFACE, with `Connection/Mapping.lean` (how code values map to spec values) and
`Connection/Hypotheses.lean` (the hypotheses). Proofs are in `Connection/Proofs/` and are
not for review: each theorem here is proved by one line pointing to its proof, so what is
reviewed is exactly what was proved.

Each theorem is a commuting square (the approach of the SymCrypt verification): run one
function of the code model, map its inputs to the spec's values, and compare its result with
the spec predicate or function there.

    code inputs ──── code function ────▶  ok r
         │                                  ‖
      mapping                               ‖
         ▼                                  ‖
    spec inputs ──── spec predicate ───▶  ok (decide _)

Where a theorem has hypotheses, the code and the spec agree only under them; outside them
they may differ, and the hypothesis says exactly where. -/

namespace Connection

/-! ## The program's checks -/

/-- **FINDING L1: `check_public_amount` does NOT compute the spec's checks.** It checks
    `pubAmtConsistent` and `amountsInRange` (only `extAmt ≠ −2^63` is a real check; the rest
    holds by the types). The square `check_public_amount … = ok (decide (pubAmtConsistent … ∧
    amountsInRange …))` is false. -/
theorem checkPublicAmount_connection_fails :
    ¬ ∀ (extAmount : I64) (fee : U64) (pa : Std.Array U8 32#usize),
      zkcash_core.utils.check_public_amount arkFr extAmount fee pa
        = ok (decide (LeanSpec.pubAmtConsistent extAmount.val fee.val (toF pa) ∧ LeanSpec.amountsInRange extAmount.val fee.val)) :=
  checkPublicAmount_not_square

/-- **L1, the counterexample.** An internal transfer (amount 0, fee 0, public amount 0):
    the spec allows it, the code rejects it. -/
theorem checkPublicAmount_L1_counterexample :
    zkcash_core.utils.check_public_amount arkFr 0#i64 0#u64 zeroBytes = ok false ∧
      LeanSpec.pubAmtConsistent (0#i64).val (0#u64).val (toF zeroBytes) ∧
        LeanSpec.amountsInRange (0#i64).val (0#u64).val :=
  checkPublicAmount_L1

/-- **L1 is the only difference.** The code computes the two spec checks and `extAmt ≠ 0`.
    This describes the finding; it is not the connection theorem. -/
theorem checkPublicAmount_differs_only_at_zero (extAmount : I64) (fee : U64)
    (pa : Std.Array U8 32#usize) :
    zkcash_core.utils.check_public_amount arkFr extAmount fee pa
      = ok (decide (LeanSpec.pubAmtConsistent extAmount.val fee.val (toF pa) ∧ LeanSpec.amountsInRange extAmount.val fee.val ∧
          extAmount.val ≠ 0)) :=
  checkPublicAmount_eq extAmount fee pa

/-- **`is_known_root` computes `rootBytesKnown`**: the root's bytes are canonical and their
    value is a non-zero root in the history. For a tree of the fixed shape (`hshape`, a proved
    invariant: `WellFormed.tree`) whose history slots all hold canonical bytes (big-endian
    value below the field modulus). `hhist` is a proved invariant for the program's tree:
    `storedRoots_canonical_reachable` proves it in every state an execution reaches.
    The code compares bytes and the spec compares values; with non-canonical stored bytes two
    different byte strings could stand for the same root. -/
theorem isKnownRoot_connection (t : zkcash_core.merkle_tree.MerkleTreeAccount)
    (root : Std.Array U8 32#usize) (hshape : TreeShape t)
    (hhist : ∀ j : Fin 100, Canonical t.root_history.val[j.val]!) :
    zkcash_core.merkle_tree.is_known_root t root
      = ok (decide (LeanSpec.rootBytesKnown (toTree t) (toBytes root.val))) :=
  isKnownRoot_eq t root hshape hhist

/-- **`validate_fee` accepts exactly when `feeSufficient` and `amountsInRange` hold**, for a
    config whose two fee rates and fee error margin are at most 100% (a proved invariant,
    `WellFormed.config`; `update_global_config` refuses more). Of `amountsInRange`, only
    `extAmt ≠ −2^63` is a real check: the rest holds by the types. -/
theorem validateFee_connection (extAmt : I64) (fee : U64) (c : zkcash_core.admin.GlobalConfig)
    (t : zkcash_core.merkle_tree.MerkleTreeAccount)
    (hd : c.deposit_fee_rate.val ≤ 10000) (hw : c.withdrawal_fee_rate.val ≤ 10000)
    (hm : c.fee_error_margin.val ≤ 10000) :
    zkcash_core.utils.validate_fee extAmt fee c.deposit_fee_rate c.withdrawal_fee_rate
        c.fee_error_margin = ok (.Ok ()) ↔
      extAmt.val ≠ -9223372036854775808 ∧ LeanSpec.feeSufficient (toConfig c t) extAmt.val fee.val :=
  validateFee_iff extAmt fee c t hd hw hm

/-- **`calculate_complete_ext_data_hash` hashes exactly the spec's serialization of the
    external data** (`serealizeExternalData`), and returns `none` exactly when an encrypted
    output is too long for the spec (`encOutsFit` fails). Here `inputs` is any spec
    transaction whose recipient, amount, encrypted outputs, fee, fee recipient and mint are
    the code's arguments, mapped. Nothing is assumed about SHA-256: this says which bytes
    are hashed. One hypothesis: the serialized data fits in a vector (120 bytes plus the two
    encrypted outputs at most the largest `usize`; every real transaction is at most 1232
    bytes). -/
theorem extDataHash_connection (sha : zkcash_core.ext_data.Sha256 Unit)
    (recipient feeRecipient mint : Pubkey) (ext : I64) (out1 out2 : Slice U8) (fee : U64)
    (inputs : LeanSpec.TxInputs)
    (hA : inputs.A = toPubkey recipient) (hext : inputs.extAmt = ext.val)
    (he0 : inputs.encOut0 = toBytes out1.val) (he1 : inputs.encOut1 = toBytes out2.val)
    (hf : inputs.f = fee.val) (ht : inputs.t = toPubkey feeRecipient)
    (hm : inputs.mintAddr = toPubkey mint)
    (hfit : out1.length + out2.length + 120 ≤ Usize.max) :
    zkcash_core.ext_data.calculate_complete_ext_data_hash sha recipient ext out1 out2 fee
        feeRecipient mint
      = if LeanSpec.encOutsFit inputs then
          (do let h ← sha.hash (toSlice (LeanSpec.serealizeExternalData inputs)); ok (some h))
        else ok none :=
  extDataHash_eq sha recipient feeRecipient mint ext out1 out2 fee inputs hA hext he0 he1 hf ht hm hfit

/-! ## The verifier, without any assumption about the syscalls -/

/-- **If the program's verifier accepts a proof, its 7 public inputs (root, public amount,
    external data hash, the two nullifiers, the two output commitments) are canonical**, so
    `toF` maps them to distinct field elements exactly when they are distinct bytes. Holds
    whatever the `alt_bn128` syscalls return: the range check comes first. -/
theorem verifyProof_canonical_connection {Cb : Type} (B : zkcash_core.groth16.Bn254 Cb)
    (proof : zkcash_core.transact.Proof) (vk : zkcash_core.groth16.VerifyingKey)
    (h : zkcash_core.groth16.verify_proof B proof vk = ok true) :
    ∀ j, j < 7 → Canonical ((publicInputs proof)[j]!) :=
  verifyProof_canonical B proof vk h

/-! ## The Merkle tree -/

section
variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-- **If `append` returns `Ok`, the new tree is the spec's `appendEffects`** of the leaf, for a
    tree of the fixed shape, under `HashesAgree` (the code's Poseidon and zero hashes are the
    spec's `H2` and `Z`). Also: there was room (`next_index < 2^26`), the index went up by one,
    the tree keeps its shape, and the fields `append` should not touch are unchanged. -/
theorem append_connection (c : Crypto) (hashes : HashesAgree c) (leaf : Std.Array U8 32#usize)
    (t t' : zkcash_core.merkle_tree.MerkleTreeAccount) (p : alloc.vec.Vec (Std.Array U8 32#usize))
    (hshape : TreeShape t)
    (h : zkcash_core.merkle_tree.append c.hasher leaf t = ok (.Ok p, t')) :
    toTree t' = LeanSpec.appendEffects (toF leaf) (toTree t) ∧ TreeShape t' ∧
      t.next_index.val < 2 ^ 26 ∧ t'.next_index.val = t.next_index.val + 1 ∧
      t'.authority = t.authority ∧ t'.max_deposit_amount = t.max_deposit_amount ∧
      t'.bump = t.bump :=
  append_ok' c hashes leaf t t' p hshape h

end

/-- **With no room, `append` returns `MerkleTreeFull` and leaves the tree unchanged**, for a
    tree of height 26 (`2^26` leaves). Any hasher. -/
theorem append_full_connection (H : zkcash_core.merkle_tree.Hasher Unit)
    (leaf : Std.Array U8 32#usize) (t : zkcash_core.merkle_tree.MerkleTreeAccount)
    (hheight : t.height.val = 26) (hfull : 2 ^ 26 ≤ t.next_index.val) :
    zkcash_core.merkle_tree.append H leaf t
      = ok (.Err zkcash_core.error.ErrorCode.MerkleTreeFull, t) :=
  append_full H leaf t hheight hfull

/-! ## The whole instruction: `transact` -/

section
variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha] [LeanSpec.Groups]
  [AddCommGroup LeanSpec.G1] [Module LeanSpec.F LeanSpec.G1] [AddCommGroup LeanSpec.G2]
  [Module LeanSpec.F LeanSpec.G2] [CommGroup LeanSpec.GT] [LeanSpec.Pairing] [LeanSpec.Deployment]

/-- **If the code model accepts a `transact` instruction, the spec's `transact` holds** between
    the world before and the world after (mapped by `toWorld`, `Connection/Mapping.lean`), for
    the transaction mapped by `toInputs`: every spec precondition held, and the new world is
    exactly the spec's `transactEffects`. The spent set grows by the two input nullifiers, and
    the new state is again `WellFormed`, so the theorem applies to the next transaction.

    The hypotheses are in `Connection/Hypotheses.lean`: `HashesAgree`, `SolanaFacts` and
    `CryptoFacts` are assumed; `WellFormed` is an invariant (proved for every reachable state
    by `wellFormed_reachable`); `OutsideSpecDetail` rules out Solana details the spec does
    not model, by design. `hProofValid` stands for the verifier bridge, which
    `transact_connection_verified` supplies; it is the only link between the spec's groups
    here (any) and the proof's bytes.

    Scope: safety. Nothing is claimed about transactions the code rejects. -/
theorem transact_connection
    {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d.crypto)
    (wf : WellFormed d spent s)
    (solana : SolanaFacts rent out1 out2)
    (crypto : CryptoFacts d proof)
    (outside : OutsideSpecDetail d rent s tx a proof)
    (hProofValid : d.crypto.proofVerifier.verify proof = ok true →
      LeanSpec.proofValid (toInputs a proof extAmount fee out1 out2)) :
    let inputs := toInputs a proof extAmount fee out1 out2
    let spent' := spent ∪ {inputs.k0, inputs.k1}
    LeanSpec.transact inputs (toWorld d rent spent s) (toWorld d rent spent' s') ∧
      WellFormed d spent' s' :=
  transact_refines hstep hashes wf solana crypto outside hProofValid

end

/-! ## The verifier bridge, and the main result

The spec's groups, point decoding, pairing and key are those of the `alt_bn128` syscalls and
the program's key (`syscallGroups`, `syscallPairing`, `programKey`); the proof's points are
the sender's bytes, decoded as the syscalls decode them. The syscall contracts `C` are
core-model's assumption (`AltBn128Contracts`); `PairingLaws` is in
`Connection/Hypotheses.lean`. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT]

/-- **If the program's verifier accepts a proof, the spec's `proofValid` holds** for the mapped
    transaction: the proof's point bytes decode (as the syscalls decode them), and the program
    computes `e(A, B) = e(α, β) · e(vk_x, γ) · e(C, δ)` with `vk_x = IC₀ + Σ xᵢ · ICᵢ₊₁` over
    the public inputs in circuit order, exactly as the spec's `Groth16.verify`. -/
theorem verifier_bridge_connection (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) (proof : zkcash_core.transact.Proof)
    (h : c.proofVerifier.verify proof = ok true)
    (a : TransactAccounts) (ext : I64) (fee : U64) (out1 out2 : Slice U8) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    LeanSpec.proofValid (toInputs a proof ext fee out1 out2) :=
  verifier_bridge c C laws proof h a ext fee out1 out2

/-- **If the code model accepts a `transact` instruction from a `WellFormed` state, the spec's
    `transact` holds**, with the spec instantiated by the syscalls and the program's key: every spec
    precondition held (the proof check included) and the new world is exactly the spec's
    `transactEffects`; the new state is again `WellFormed`. Same as `transact_connection`, with
    its temporary `hProofValid` replaced by the syscall contracts `C` and `PairingLaws`. -/
theorem transact_connection_verified [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d.crypto)
    (wf : WellFormed d spent s)
    (solana : SolanaFacts rent out1 out2)
    (crypto : CryptoFacts d proof)
    (outside : OutsideSpecDetail d rent s tx a proof) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2
    let spent' := spent ∪ {inputs.k0, inputs.k1}
    LeanSpec.transact inputs (toWorld d rent spent s) (toWorld d rent spent' s') ∧
      WellFormed d spent' s' :=
  transact_refines_verified C laws hstep hashes wf solana crypto outside

end

/-! ## `WellFormed` holds of every reachable state -/

/-- **Every state an execution of the code model reaches from genesis is `WellFormed`**, for
    the nullifiers spent by the execution's `transact` instructions (`runSpent`). Executions
    are core-model's `Run`: any mix of `initialize`, `update_deposit_limit`,
    `update_global_config`, `transact` and outside actions. Hypotheses: the program is not
    the system program (asm), and `HashesAgree` (asm), of which only the two canonicity
    fields are used: stored roots are zero hashes, zero bytes or Poseidon outputs. -/
theorem wellFormed_reachable [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    {d : Deployment} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (hashes : HashesAgree d.crypto) :
    WellFormed d (runSpent evs) s :=
  wf_reachable hgen hrun hpid hashes

/-- **In every state an execution reaches from genesis, every tree the program owns stores
    only canonical roots**: the hypothesis `hhist` of `isKnownRoot_connection` holds of the
    program's tree. Hypotheses as `wellFormed_reachable`. -/
theorem storedRoots_canonical_reachable [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    {d : Deployment} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (hashes : HashesAgree d.crypto) :
    ∀ k t, HoldsTree d.programId s k t → ∀ j : Fin 100, Canonical t.root_history.val[j.val]! :=
  storedRoots_reachable hgen hrun hpid hashes

/-! ## MAIN RESULT -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT]

/-- **MAIN RESULT. In every execution of the code model from genesis, every `transact` the code
    accepts satisfies the spec's `transact`**: every spec precondition held (the proof check
    included) and the new world is exactly the spec's `transactEffects`. The spec's nullifier
    set is the one the execution spent before this transaction.

    Hypotheses (`Connection/Hypotheses.lean`): the execution (`hgen`, `hrun`, the step
    `hstep`); the program is not the system program; `HashesAgree`, `SolanaFacts`,
    `CryptoFacts`, the syscall contracts `C` and `PairingLaws` (assumed); `OutsideSpecDetail`
    (Solana details the spec does not model, by design). No code/spec difference is excluded.
    `WellFormed` is no longer a hypothesis: it is proved. -/
theorem transact_connection_main [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    {d : Deployment} {rent : Nat → U64} {s₀ s s' : State} {evs : List Event} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hashes : HashesAgree d.crypto)
    (solana : SolanaFacts rent out1 out2)
    (crypto : CryptoFacts d proof)
    (outside : OutsideSpecDetail d rent s tx a proof) :
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2
    LeanSpec.transact inputs (toWorld d rent (runSpent evs) s)
      (toWorld d rent (runSpent evs ∪ {inputs.k0, inputs.k1}) s') :=
  (transact_refines_verified C laws hstep hashes (wf_reachable hgen hrun hpid hashes) solana crypto
    outside).1

end


/-! ## Handler completeness: the program's own logic accepts what the spec allows

`execTransact` runs Anchor's checks and `init`s, then the handler (the extracted
`zkcash_core::transact::transact`), then the runtime's lamport check. These theorems cover the
handler only: the spec world is the one the handler sees (`handlerWorld`: after Anchor's
`init`s, so no nullifier rent), on the environment `execTransact` builds (`handlerEnv`).
Anchor and the runtime are future work. -/

/-- **Handler completeness, with an exclusion `excl`**: for any deployment satisfying the
    assumptions, if the spec's preconditions hold for the mapped transaction in the world the
    handler sees, and `excl` holds, the handler returns `Ok`, every balance is the spec's
    (`transactEffects`, on code addresses) and the new tree is the spec's.

    Hypotheses, by kind: `HashesAgree`, `HashesSucceed`, `SyscallsSucceed` (asm), `PairingLaws`
    (asm), `KeyG2Decodes` (asm); tree shape, canonical history and subtrees, config rates at most
    100% (inv: `WellFormed`); the signer is a system account with no data (premise: Anchor's
    `init` of the nullifier accounts, paid by the signer, requires it); the serialized external
    data fits in a vector (asm, `SolanaFacts.fitsInVector`).

    The faithful statement is `HandlerComplete (fun _ _ => True)`; it is false. -/
def HandlerComplete (excl : I64 → zkcash_core.transact.Proof → Prop) : Prop :=
  ∀ (G1 G2 GT : Type) [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
    [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) (laws : PairingLaws C.e),
    HashesAgree c → HashesSucceed c → SyscallsSucceed C → KeyG2Decodes C →
    ∀ (a : TransactAccounts) (s₁ : State) (v : U64) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
      (config : zkcash_core.admin.GlobalConfig) (spent : Finset LeanSpec.F)
      (proof : zkcash_core.transact.Proof) (ext : I64) (fee : U64) (out1 out2 : Slice U8),
    TreeShape tree → (∀ j : Fin 100, Canonical tree.root_history.val[j.val]!) →
    (∀ j : Fin 26, Canonical tree.subtrees.val[j.val]!) →
    config.deposit_fee_rate.val ≤ 10000 → config.withdrawal_fee_rate.val ≤ 10000 →
    config.fee_error_margin.val ≤ 10000 →
    ((s₁ a.signer).owner = systemProgram ∧ (s₁ a.signer).data.isEmpty) →
    out1.length + out2.length + 120 ≤ Usize.max →
    excl ext proof →
    letI : LeanSpec.Groups := syscallGroups C
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    LeanSpec.transactPreconditions (toInputs a proof ext fee out1 out2)
      (handlerWorld a s₁ v tree config spent) →
    ∃ ap env' tree', zkcash_core.transact.transact c.hasher arkFr c.sha256 c.proofVerifier solRuntime
      (handlerEnv a s₁ v) tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2
      = ok (.Ok ap, env', tree') ∧
      (∀ k, (env'.balances k).val
        = (LeanSpec.transactEffects (toInputs a proof ext fee out1 out2)
            (handlerWorld a s₁ v tree config spent)).balances (toPubkey k)) ∧
      toTree tree' = (LeanSpec.transactEffects (toInputs a proof ext fee out1 out2)
        (handlerWorld a s₁ v tree config spent)).state.tree

/-- **FINDING L1: the handler is NOT complete.** The faithful statement is false. Counterexample
    (`Toy.toy_pre_L1`, `Toy.toy_L1_rejects`): in a toy deployment satisfying every assumption, an
    internal transfer (amount 0, fee 0) meets every spec precondition and the handler rejects it
    (`check_public_amount`). -/
theorem handlerComplete_connection_fails : ¬ HandlerComplete (fun _ _ => True) := by
  intro h
  letI := Toy.toyPoseidon
  letI := Toy.toySpecSha
  exact Toy.toy_refutes_L1 (h Unit Unit Unit Toy.toyCrypto Toy.toyC Toy.toyLaws Toy.toyHashesAgree
    Toy.toyHashesSucceed Toy.toySyscalls Toy.toyKey Toy.toyAccounts (Toy.toyState 0#u64) 0#u64
    Toy.toyTree Toy.toyConfig ∅ _ 0#i64 0#u64 Toy.emptySlice Toy.emptySlice Toy.toyTree_shape
    Toy.toyTree_hist Toy.toyTree_sub (by simp [Toy.toyConfig]) (by simp [Toy.toyConfig])
    (by simp [Toy.toyConfig]) ⟨rfl, rfl⟩ Toy.toyFit trivial)

/-- **PROPOSED FINDING A0: excluding L1 is not enough.** With only `extAmt ≠ 0` excluded the
    statement is still false. Counterexample (`Toy.toy_pre_A0`, `Toy.toy_A0_rejects`): a deposit
    whose `proof_a` is the 64 zero bytes, which the syscalls (so the spec's decoding) read as the
    identity point; `negate_g1` decodes with arkworks, which rejects them, so the verifier fails. -/
theorem handlerComplete_without_L1_fails :
    ¬ HandlerComplete (fun ext _ => ext.val ≠ 0) := by
  intro h
  letI := Toy.toyPoseidon
  letI := Toy.toySpecSha
  exact Toy.toy_refutes_A0 (h Unit Unit Unit Toy.toyCrypto Toy.toyC Toy.toyLaws Toy.toyHashesAgree
    Toy.toyHashesSucceed Toy.toySyscalls Toy.toyKey Toy.toyAccounts (Toy.toyState 1#u64) 0#u64
    Toy.toyTree Toy.toyConfig ∅ _ 1#i64 0#u64 Toy.emptySlice Toy.emptySlice Toy.toyTree_shape
    Toy.toyTree_hist Toy.toyTree_sub (by simp [Toy.toyConfig]) (by simp [Toy.toyConfig])
    (by simp [Toy.toyConfig]) ⟨rfl, rfl⟩ Toy.toyFit (by simp))

/-- **L1 and A0 are the only differences.** With `extAmt ≠ 0` and `proof_a` not the 64 zero
    bytes, the handler is complete: it returns `Ok` with exactly the spec's transfer, fee and tree
    effects. This describes the findings; the faithful statement is
    `handlerComplete_connection_fails`. -/
theorem handlerComplete_differs_only_at_L1_A0 :
    HandlerComplete (fun ext proof => ext.val ≠ 0 ∧ proof.proof_a.val ≠ List.replicate 64 0#u8) := by
  intro G1 G2 GT _ _ _ _ _ _ _ c C laws hashes succ sys key a s₁ v tree config spent proof ext fee
    out1 out2 hshape hhist hsub hd hw hm hsigner hfit hex
  exact handler_complete_exact' c C laws hashes succ sys key a s₁ v tree config spent proof ext fee
    out1 out2 hshape hhist hsub hd hw hm hsigner hfit hex.1 hex.2

/-- **Subtrees are canonical in every reachable state** (the hypothesis on subtrees of
    `HandlerComplete` holds of every tree the program owns). Hypotheses as
    `wellFormed_reachable`. -/
theorem storedSubtrees_canonical_reachable [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
    {d : Deployment} {s₀ s : State} {evs : List Event}
    (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
    (hashes : HashesAgree d.crypto) :
    ∀ k t, HoldsTree d.programId s k t → ∀ j : Fin 26, Canonical t.subtrees.val[j.val]! :=
  (wf_reachable hgen hrun hpid hashes).storedSubtrees


/-! ## Non-vacuity: the hypotheses of the main result can hold together

If the hypotheses of `transact_connection_main`, as written in Lean, could never hold together,
the theorem would say nothing. In a deliberately broken toy deployment (`Proofs/Toy.lean`:
`G1 = G2 = GT = Unit`, every pairing 1, Poseidon always 1, SHA-256 always zero; the G1 decoding
is the real one) and a toy PDA derivation, one execution (genesis, `initialize`, a deposit of 1
lamport) is accepted by `step`, and every hypothesis of the main result holds for the deposit.
The toy syscalls answer exactly when their points decode: syscalls that always fail would also
satisfy core-model's contracts, but every proof would then fail. -/

/-- **The main result is not vacuous.** A deployment, an execution from genesis and an accepted
    deposit for which every hypothesis of `transact_connection_main` holds, together with the
    completeness bundles (`HashesSucceed`, `SyscallsSucceed`, `KeyG2Decodes`). -/
theorem connection_nonvacuous :
    ∃ (d : Deployment) (rent : Nat → U64) (s₀ s s' : State) (evs : List Event) (tx : TxEnv)
      (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64)
      (out1 out2 : Slice U8) (events : List CommitmentData)
      (C : AltBn128Contracts d.crypto.altBn128 Unit Unit Unit) (laws : PairingLaws C.e),
      Genesis d.programId s₀ ∧ Run d s₀ evs s ∧ d.programId ≠ systemProgram ∧
      step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events) ∧ extAmount.val > 0 ∧
      @HashesAgree Toy.toyPoseidon Toy.toySpecSha d.crypto ∧ SolanaFacts rent out1 out2 ∧
      CryptoFacts d proof ∧ OutsideSpecDetail d rent s tx a proof ∧
      HashesSucceed d.crypto ∧ SyscallsSucceed C ∧ KeyG2Decodes C := by
  obtain ⟨s, s', evs, events, h1, h2, h3, h4, h5, h6, h7, h8⟩ := Toy.toy_execution
  exact ⟨Toy.toyD, Toy.toyRent, Toy.toyS0, s, s', evs, Toy.toyTx, Toy.depA, Toy.depProof, 1#i64, 0#u64,
    Toy.emptySlice, Toy.emptySlice, events, Toy.toyC, Toy.toyLaws, h1, h2, h3, h4, by simp, h5, h6, h7, h8,
    Toy.toyHashesSucceed, Toy.toySyscalls, Toy.toyKey⟩

end Connection
