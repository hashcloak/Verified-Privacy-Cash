import Connection.ConnectionTheorems
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Findings

REVIEW SURFACE for the findings: differences between the code and the spec, shown by
theorems. A difference makes the faithful theorem fail, so each finding is stated as a
counterexample (the code rejects what the spec allows) and, where known, as an exact
statement of where code and spec differ. Details and recommendations are in `FINDINGS.md`.

- **L1**: the code rejects a zero external amount (an internal transfer), which the docs and
  the spec allow. At the level of `check_public_amount`, and of the handler.
- **A0**: the code rejects a proof whose `proof_a` is the 64 zero bytes, which the syscalls
  (and so the spec) read as the identity point: `negate_g1` decodes with arkworks.
-/

namespace Connection

/-! ## L1 at the level of `check_public_amount` -/

/-- **L1, counterexample at the level of `check_public_amount`.** An internal transfer (amount
    0, fee 0, public amount 0): the spec's checks hold, the code rejects it. -/
theorem checkPublicAmount_L1_counterexample :
    zkcash_core.utils.check_public_amount arkFr 0#i64 0#u64 zeroBytes = ok false ∧
      LeanSpec.pubAmtConsistent (0#i64).val (0#u64).val (toF zeroBytes) ∧
        LeanSpec.amountsInRange (0#i64).val (0#u64).val :=
  checkPublicAmount_L1

/-! ## Handler completeness: L1 and A0, and nothing else

`execTransact` runs Anchor's checks and `init`s, then the handler (the extracted
`zkcash_core::transact::transact`), then the runtime's lamport check. These theorems cover
the handler only: the spec world is the one the handler sees (`handlerWorld`: after
Anchor's `init`s, so no nullifier rent), on the environment `execTransact` builds
(`handlerEnv`). -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-- `HandlerSpecAllows …`: the spec allows the transaction: every spec precondition holds
    for the mapped inputs in the world the handler sees. -/
def HandlerSpecAllows (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (a : TransactAccounts) (s₁ : State) (v : U64) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
    (config : zkcash_core.admin.GlobalConfig) (spent : Finset LeanSpec.F)
    (proof : zkcash_core.transact.Proof) (ext : I64) (fee : U64) (out1 out2 : Slice U8) : Prop :=
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  LeanSpec.transactPreconditions (toInputs a proof ext fee out1 out2) (handlerWorld a s₁ v tree config spent)

/-- `HandlerMatchesSpec …`: the handler accepts, with exactly the spec's effects: it returns
    `Ok`, every account's balance is the spec's (`transactEffects`, on code addresses), and
    the new tree is the spec's. -/
def HandlerMatchesSpec (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (a : TransactAccounts) (s₁ : State) (v : U64) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
    (config : zkcash_core.admin.GlobalConfig) (spent : Finset LeanSpec.F)
    (proof : zkcash_core.transact.Proof) (ext : I64) (fee : U64) (out1 out2 : Slice U8) : Prop :=
  letI : LeanSpec.Groups := syscallGroups C
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  let effects := LeanSpec.transactEffects (toInputs a proof ext fee out1 out2)
    (handlerWorld a s₁ v tree config spent)
  ∃ ap env' tree', zkcash_core.transact.transact c.hasher arkFr c.sha256 c.proofVerifier solRuntime
      (handlerEnv a s₁ v) tree config proof ext fee a.recipient a.feeRecipientAccount out1 out2
      = ok (.Ok ap, env', tree') ∧
    (∀ k, (env'.balances k).val = effects.balances (toPubkey k)) ∧ toTree tree' = effects.state.tree

end

section
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha

/-- **FINDING L1, counterexample: the handler rejects an internal transfer.** In a toy
    deployment (`Connection/Proofs/Toy.lean`) satisfying the completeness assumptions and the
    handler's context, the spec allows an internal transfer (amount 0, fee 0), and the
    handler rejects it (`check_public_amount`). -/
theorem handler_rejects_internal_transfer :
    CompletenessAssumptions Toy.toyCrypto Toy.toyC ∧
    HandlerContext Toy.toyAccounts (Toy.toyState 0#u64) Toy.toyTree Toy.toyConfig Toy.emptySlice Toy.emptySlice ∧
    HandlerSpecAllows Toy.toyCrypto Toy.toyC Toy.toyLaws Toy.toyAccounts (Toy.toyState 0#u64) 0#u64
      Toy.toyTree Toy.toyConfig ∅ Toy.l1Proof 0#i64 0#u64 Toy.emptySlice Toy.emptySlice ∧
    ¬ HandlerMatchesSpec Toy.toyCrypto Toy.toyC Toy.toyLaws Toy.toyAccounts (Toy.toyState 0#u64) 0#u64
      Toy.toyTree Toy.toyConfig ∅ Toy.l1Proof 0#i64 0#u64 Toy.emptySlice Toy.emptySlice :=
  ⟨Toy.toyAssumptions, Toy.toyContext _, Toy.toy_pre_L1, fun ⟨ap, e, t, h, _⟩ => Toy.toy_L1_rejects ap e t h⟩

/-- **FINDING A0, counterexample: the handler rejects an identity `proof_a`.** Excluding L1
    is not enough. In the same toy deployment, the spec allows a deposit (amount 1, so not
    L1) whose `proof_a` is the 64 zero bytes, which the syscalls, and so the spec's decoding,
    read as the identity point; the handler rejects it (`negate_g1` decodes with arkworks,
    which rejects those bytes). -/
theorem handler_rejects_zero_proof_a :
    (1#i64 : I64).val ≠ 0 ∧
    CompletenessAssumptions Toy.toyCrypto Toy.toyC ∧
    HandlerContext Toy.toyAccounts (Toy.toyState 1#u64) Toy.toyTree Toy.toyConfig Toy.emptySlice Toy.emptySlice ∧
    HandlerSpecAllows Toy.toyCrypto Toy.toyC Toy.toyLaws Toy.toyAccounts (Toy.toyState 1#u64) 0#u64
      Toy.toyTree Toy.toyConfig ∅ Toy.a0Proof 1#i64 0#u64 Toy.emptySlice Toy.emptySlice ∧
    ¬ HandlerMatchesSpec Toy.toyCrypto Toy.toyC Toy.toyLaws Toy.toyAccounts (Toy.toyState 1#u64) 0#u64
      Toy.toyTree Toy.toyConfig ∅ Toy.a0Proof 1#i64 0#u64 Toy.emptySlice Toy.emptySlice :=
  ⟨by simp, Toy.toyAssumptions, Toy.toyContext _, Toy.toy_pre_A0,
    fun ⟨ap, e, t, h, _⟩ => Toy.toy_A0_rejects ap e t h⟩

end

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-- **FINDINGS L1 and A0, and they are the only differences.** Handler completeness (if the
    spec allows a transaction, the handler accepts it with exactly the spec's effects) fails
    in exactly two cases:
    - **L1:** a zero amount (an internal transfer);
    - **A0:** `proof_a` is the 64 zero bytes.
    The counterexamples above show both happen; this theorem shows nothing else does: with a
    nonzero amount and `proof_a` not the 64 zero bytes, the handler is complete. It covers
    the handler only (the program's own logic), not Anchor's checks or the runtime. -/
theorem handler_complete_except_L1_A0 (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) {a : TransactAccounts} {s₁ : State} {v : U64}
    {tree : zkcash_core.merkle_tree.MerkleTreeAccount} {config : zkcash_core.admin.GlobalConfig}
    {spent : Finset LeanSpec.F} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8}
    (assume : CompletenessAssumptions c C)                 -- [assumed] see the structure
    (ctx : HandlerContext a s₁ tree config out1 out2)      -- [invariant], [premise]: see the structure
    (notL1 : ext.val ≠ 0)                                  -- [finding L1] excluded
    (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8)   -- [finding A0] excluded
    (allows : HandlerSpecAllows c C laws a s₁ v tree config spent proof ext fee out1 out2) :
                                                           -- [premise] the spec allows it
    HandlerMatchesSpec c C laws a s₁ v tree config spent proof ext fee out1 out2 :=
  handler_complete_exact' c C laws assume.1 assume.2 assume.3 assume.4 a s₁ v tree config spent proof ext
    fee out1 out2 ctx.1 ctx.2 ctx.3 ctx.4 ctx.5 ctx.6 ctx.7 ctx.8 notL1 notA0 allows

end

end Connection
