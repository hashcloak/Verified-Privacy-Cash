import Connection.ConnectionTheorems
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Findings

REVIEW SURFACE for the findings: differences between the code and the spec, shown by
theorems. A difference makes the faithful theorem fail, so each finding is stated as a
counterexample (the code rejects what the spec allows). That these are the only differences
at the handler is `handler_complete_except_L1_A0` (`ConnectionTheorems.lean`, section 1b).
Details and recommendations are in `FINDINGS.md`.

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

/-! ## L1 and A0 at the level of the handler

Counterexamples to handler completeness (`handler_complete_except_L1_A0` in
`ConnectionTheorems.lean`): it fails in exactly these two cases. -/

section
attribute [local instance] Toy.toyPoseidon Toy.toySpecSha

/-- **FINDING L1, counterexample: the handler rejects an internal transfer.** In a toy
    deployment (`Connection/Proofs/Toy.lean`) satisfying the completeness assumptions and the
    handler's context, the spec allows an internal transfer (amount 0, fee 0), and the
    handler rejects it (`check_public_amount`). -/
theorem handler_rejects_internal_transfer
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    CompletenessAssumptions Toy.toyCrypto Toy.toyC ∧
    HandlerContext Toy.toyAccounts (Toy.toyState 0#u64) Toy.toyTree Toy.toyConfig ∧
    HandlerSpecAllows Toy.toySigners Toy.toyCrypto Toy.toyC Toy.toyAccounts (Toy.toyState 0#u64) 0#u64
      Toy.toyTree Toy.toyConfig ∅ Toy.l1Proof 0#i64 0#u64 Toy.emptySlice Toy.emptySlice ∧
    ¬ HandlerMatchesSpec Toy.toySigners Toy.toyCrypto Toy.toyC Toy.toyAccounts (Toy.toyState 0#u64) 0#u64
      Toy.toyTree Toy.toyConfig ∅ Toy.l1Proof 0#i64 0#u64 Toy.emptySlice Toy.emptySlice :=
  ⟨Toy.toyAssumptions h64, Toy.toyContext _, Toy.toy_pre_L1, fun ⟨ap, e, t, h, _⟩ => Toy.toy_L1_rejects ap e t h⟩

/-- **FINDING A0, counterexample: the handler rejects an identity `proof_a`.** Excluding L1
    is not enough. In the same toy deployment, the spec allows a deposit (amount 1, so not
    L1) whose `proof_a` is the 64 zero bytes, which the syscalls, and so the spec's decoding,
    read as the identity point; the handler rejects it (`negate_g1` decodes with arkworks,
    which rejects those bytes). -/
theorem handler_rejects_zero_proof_a
    (h64 : Usize.max = 2 ^ 64 - 1) :                      -- `usize` is 64 bits, as on Solana
    (1#i64 : I64).val ≠ 0 ∧
    CompletenessAssumptions Toy.toyCrypto Toy.toyC ∧
    HandlerContext Toy.toyAccounts (Toy.toyState 1#u64) Toy.toyTree Toy.toyConfig ∧
    HandlerSpecAllows Toy.toySigners Toy.toyCrypto Toy.toyC Toy.toyAccounts (Toy.toyState 1#u64) 0#u64
      Toy.toyTree Toy.toyConfig ∅ Toy.a0Proof 1#i64 0#u64 Toy.emptySlice Toy.emptySlice ∧
    ¬ HandlerMatchesSpec Toy.toySigners Toy.toyCrypto Toy.toyC Toy.toyAccounts (Toy.toyState 1#u64) 0#u64
      Toy.toyTree Toy.toyConfig ∅ Toy.a0Proof 1#i64 0#u64 Toy.emptySlice Toy.emptySlice :=
  ⟨by simp, Toy.toyAssumptions h64, Toy.toyContext _, Toy.toy_pre_A0,
    fun ⟨ap, e, t, h, _⟩ => Toy.toy_A0_rejects ap e t h⟩

end

end Connection
