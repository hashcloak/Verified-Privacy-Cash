import Connection.Proofs.Checks
import Connection.Proofs.ExtData
import Connection.Proofs.Tree
import Connection.Proofs.Verifier
import Connection.Proofs.Transact
import Connection.Proofs.Bridge
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Connection theorems

REVIEW SURFACE, with `Connection/Mapping.lean` (how code values map to spec values) and
`Connection/Assumptions.lean` (what is assumed). Proofs are in `Connection/Proofs/` and are
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

/-- **`check_public_amount` computes `pubAmtConsistent`.** For every amount, fee and
    public-amount bytes, the code returns the spec predicate's truth value. No hypotheses. -/
theorem checkPublicAmount_connection (extAmount : I64) (fee : U64) (pa : Std.Array U8 32#usize) :
    zkcash_core.utils.check_public_amount arkFr extAmount fee pa
      = ok (decide (LeanSpec.pubAmtConsistent extAmount.val fee.val (toF pa))) :=
  checkPublicAmount_eq extAmount fee pa

/-- **`is_known_root` computes `rootKnown`**, for a tree of the fixed shape and canonical
    bytes (big-endian value below the field modulus) for the root and every history slot.
    The code compares bytes and the spec compares field elements; with non-canonical bytes
    two different byte strings can be the same field element. -/
theorem isKnownRoot_connection (t : zkcash_core.merkle_tree.MerkleTreeAccount)
    (root : Std.Array U8 32#usize) (hshape : TreeShape t) (hroot : Canonical root)
    (hhist : ∀ j : Fin 100, Canonical t.root_history.val[j.val]!) :
    zkcash_core.merkle_tree.is_known_root t root
      = ok (decide (LeanSpec.rootKnown (toTree t) (toF root))) :=
  isKnownRoot_eq t root hshape hroot hhist

/-- **If `is_known_root` accepts, `rootKnown` holds**, for a tree of the fixed shape and a
    canonical root. Needs nothing about the history (unlike the theorem above). -/
theorem isKnownRoot_accepts (t : zkcash_core.merkle_tree.MerkleTreeAccount)
    (root : Std.Array U8 32#usize) (hshape : TreeShape t) (hroot : Canonical root)
    (h : zkcash_core.merkle_tree.is_known_root t root = ok true) :
    LeanSpec.rootKnown (toTree t) (toF root) :=
  isKnownRoot_safe t root hshape hroot h

/-- **`validate_fee` accepts exactly when `feeSufficient` holds and the amount is not
    `i64::MIN`**, for a config whose two fee rates and fee error margin are at most 100%
    (`update_global_config` refuses more). Outside these bounds the code's arithmetic
    truncates or overflows and differs from the spec.
    DIFFERENCE: at `extAmt = i64::MIN` the code rejects (`checked_neg` overflows) where
    `feeSufficient` may hold. Harmless in `transact`: `check_public_amount` runs first and
    rejects `i64::MIN`, as does the spec's `pubAmtConsistent`. -/
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
theorem extDataHash_connection [LeanSpec.Groups] (sha : zkcash_core.ext_data.Sha256 Unit)
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

    The hypotheses are in `Connection/Assumptions.lean`: `HashesAgree` and `Trusted` are
    trusted; `WellFormed` is an invariant to be proved; `Findings` rules out the four known
    code/spec differences (CONNECTIONS.md). `hProofValid` is TEMPORARY: until the verifier
    bridge is built, the code's verifier accepting is assumed to mean the spec's `proofValid`.

    Scope: safety. Nothing is claimed about transactions the code rejects. -/
theorem transact_connection
    {d : Deployment} {rent : Nat → U64} {spent : Finset LeanSpec.F} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData} (π : LeanSpec.Groth16.Proof)
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d.crypto)
    (wf : WellFormed d spent s)
    (trusted : Trusted d rent tx proof out1 out2)
    (findings : Findings d rent s a proof extAmount fee)
    (hProofValid : d.crypto.proofVerifier.verify proof = ok true →
      LeanSpec.proofValid (toInputs a proof extAmount fee out1 out2 π)) :
    let inputs := toInputs a proof extAmount fee out1 out2 π
    let spent' := spent ∪ {inputs.k0, inputs.k1}
    LeanSpec.transact inputs (toWorld d rent spent s) (toWorld d rent spent' s') ∧
      WellFormed d spent' s' :=
  transact_refines π hstep hashes wf trusted findings hProofValid

end

/-! ## The verifier bridge, and the main result

The spec's groups, pairing, key and proof points are those of the `alt_bn128` syscalls and the
program's key (`syscallGroups`, `syscallPairing`, `programKey`, `proofPoints`). The syscall
contracts `C` are core-model's assumption (`AltBn128Contracts`); `PairingLaws` is in
`Connection/Assumptions.lean`. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT]

/-- **If the program's verifier accepts a proof, the spec's `proofValid` holds** for the mapped
    transaction: the program computes `e(A, B) = e(α, β) · e(vk_x, γ) · e(C, δ)` with
    `vk_x = IC₀ + Σ xᵢ · ICᵢ₊₁` over the public inputs in circuit order, exactly as the spec's
    `Groth16.verify`. -/
theorem verifier_bridge_connection (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) (proof : zkcash_core.transact.Proof)
    (h : c.proofVerifier.verify proof = ok true)
    (a : TransactAccounts) (ext : I64) (fee : U64) (out1 out2 : Slice U8) :
    letI : LeanSpec.Groups := syscallGroups G1 G2 GT
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    LeanSpec.proofValid (toInputs a proof ext fee out1 out2 (proofPoints C proof)) :=
  verifier_bridge c C laws proof h a ext fee out1 out2

/-- **MAIN RESULT. If the code model accepts a `transact` instruction, the spec's `transact`
    holds**, with the spec instantiated by the syscalls and the program's key: every spec
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
    (trusted : Trusted d rent tx proof out1 out2)
    (findings : Findings d rent s a proof extAmount fee) :
    letI : LeanSpec.Groups := syscallGroups G1 G2 GT
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2 (proofPoints C proof)
    let spent' := spent ∪ {inputs.k0, inputs.k1}
    LeanSpec.transact inputs (toWorld d rent spent s) (toWorld d rent spent' s') ∧
      WellFormed d spent' s' :=
  transact_refines_verified C laws hstep hashes wf trusted findings

end

end Connection
