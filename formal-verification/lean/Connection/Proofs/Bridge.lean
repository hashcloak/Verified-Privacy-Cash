import Connection.Proofs.Transact
import PrivacyCash.Proofs.Groth16
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: the verifier bridge

NOT FOR REVIEW: the statements are restated in `Connection/ConnectionTheorems.lean`.

The program's verifier (extracted `verify_proof` with the extracted key, on the `alt_bn128`
syscalls) accepts only proofs that satisfy the spec's `Groth16.verify`, once the spec's groups,
pairing and key are the syscalls' groups, the syscall pairing and the program's key. -/

namespace Connection
open PrivacyCash.Proofs.Groth16 (ic vkxOf programVerifier_groth16)

section
variable {signers : List Pubkey}
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] {s : AltBn128}

omit [Module Spec.F G1] [Inhabited G2] in
/-- The spec decodes the mapped proof's bytes as the syscalls decode the proof's points. -/
theorem decode_toInputs (C : AltBn128Contracts s G1 G2 GT) (proof : zkcash_core.transact.Proof)
    (a : TransactAccounts) (ext : I64) (fee : U64) (out1 out2 : Slice U8)
    {A Cp : G1} {B : G2} (hA : C.decodeG1 proof.proof_a = some A)
    (hB : C.decodeG2 proof.proof_b = some B) (hC : C.decodeG1 proof.proof_c = some Cp) :
    letI : Spec.Groups := syscallGroups C
    (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩).π.decode = some (Spec.Groth16.Proof.mk A B Cp) := by
  letI : Spec.Groups := syscallGroups C
  have e1 : Spec.Groups.decodeG1 (toBytes proof.proof_a.val) = some A := by
    show (toArray 64#usize (toBytes proof.proof_a.val)).bind C.decodeG1 = some A
    rw [toArray_toBytes]; exact hA
  have e2 : Spec.Groups.decodeG2 (toBytes proof.proof_b.val) = some B := by
    show (toArray 128#usize (toBytes proof.proof_b.val)).bind C.decodeG2 = some B
    rw [toArray_toBytes]; exact hB
  have e3 : Spec.Groups.decodeG1 (toBytes proof.proof_c.val) = some Cp := by
    show (toArray 64#usize (toBytes proof.proof_c.val)).bind C.decodeG1 = some Cp
    rw [toArray_toBytes]; exact hC
  simp only [Spec.Groth16.ProofBytes.decode, toInputs, e1, e2, e3]

/-- **The bridge.** If the program's verifier accepts `proof`, the spec's `proofValid` holds for
    the mapped transaction, with the spec instantiated by the syscalls and the program's key. -/
theorem verifier_bridge (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) (proof : zkcash_core.transact.Proof)
    (h : c.proofVerifier.verify proof = ok true)
    (a : TransactAccounts) (ext : I64) (fee : U64) (out1 out2 : Slice U8) :
    withSyscallSpec C in
    Spec.proofValid (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩) := by
  obtain ⟨-, -, A, Cp, α, B, β, γ, δ, d1, d2, d3, d4, d5, d6, d7, heq⟩ :=
    programVerifier_groth16 c C proof h
  withSyscallSpec C
  -- the decoded points
  have hdec : (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩).π.decode = some ⟨A, B, Cp⟩ := by
    exact decode_toInputs C proof a ext fee out1 out2 d1 d2 d3
  refine ⟨⟨A, B, Cp⟩, hdec, ?_⟩
  have hα : (C.decodeG1 zkcash_core.verifying_key.VERIFYING_KEY.vk_alpha_g1).getD 0 = α := by rw [d4]; rfl
  have hβ : (C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_beta_g2).getD default = β := by rw [d5]; rfl
  have hγ : (C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_gamme_g2).getD default = γ := by rw [d6]; rfl
  have hδ : (C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_delta_g2).getD default = δ := by rw [d7]; rfl
  -- the spec's vk_x is the code's
  have hvec : ∀ i : Fin 7, Spec.Groth16.toVector (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩).pubInputs i
      = toF ((publicInputs proof)[i.val]!) := by
    intro i; fin_cases i <;> rfl
  have hsmul : ∀ (b : Std.Array U8 32#usize) (P : G1), toF b • P = beNatOf b • P := by
    intro b P
    rw [toF_def]
    rw [Nat.cast_smul_eq_nsmul]; rfl
  have hvkx : ic C zkcash_core.verifying_key.VERIFYING_KEY 0 +
      ∑ i : Fin 7, Spec.Groth16.toVector (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩).pubInputs i •
        ic C zkcash_core.verifying_key.VERIFYING_KEY i.succ.val
      = vkxOf C zkcash_core.verifying_key.VERIFYING_KEY proof := by
    simp only [vkxOf, hvec, hsmul, Fin.val_succ]
    rw [Fin.sum_univ_eq_sum_range (fun j => beNatOf ((publicInputs proof)[j]!) •
      ic C zkcash_core.verifying_key.VERIFYING_KEY (j + 1)) 7]
  -- the equation
  show C.e A B
    = C.e ((C.decodeG1 zkcash_core.verifying_key.VERIFYING_KEY.vk_alpha_g1).getD 0)
        ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_beta_g2).getD default) *
      C.e (ic C zkcash_core.verifying_key.VERIFYING_KEY 0 +
        ∑ i : Fin 7, Spec.Groth16.toVector (toInputs ⟨⟨signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩).pubInputs i •
          ic C zkcash_core.verifying_key.VERIFYING_KEY i.succ.val)
        ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_gamme_g2).getD default) *
      C.e Cp ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_delta_g2).getD default)
  rw [hα, hβ, hγ, hδ, hvkx]
  rw [laws.neg_left] at heq
  have : (C.e A B)⁻¹ * (C.e (vkxOf C zkcash_core.verifying_key.VERIFYING_KEY proof) γ * C.e Cp δ * C.e α β) = 1 := by
    rw [← heq]; simp only [mul_assoc]
  have h2 := inv_mul_eq_one.mp this
  rw [h2]
  ac_rfl

/-- `transact_refines` with the verifier bridge in place of the temporary `hProofValid`. -/
theorem transact_refines_verified [Spec.PoseidonHashes] [Spec.Sha]
    {d : Deployment} {rent : Nat → U64} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d)
    (wf : WellFormed d s)
    (solana : PdasDoNotSign d tx.toTxContext) (hrentPos : tx.RentPositive)
    (crypto : NewNullifierAddressesDiffer d proof) (circuit : CircuitFacts d {proof})
    (rentFixed : SameRent rent tx.minimumBalance) :
    withSyscallSpec C in
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩
    Spec.transact inputs (toWorld d rent s) (toWorld d rent s') := by
  withSyscallSpec C
  exact transact_refines hstep hashes wf solana hrentPos crypto circuit rentFixed
    (fun hv => verifier_bridge d.crypto C laws proof hv a extAmount fee out1 out2) rfl

/-- `transact_refines_between` with the verifier bridge in place of `hProofValid`. -/
theorem transact_refines_between_verified [Spec.PoseidonHashes] [Spec.Sha]
    {d : Deployment} {rent : Nat → U64} {s s' : State} {tx : TxEnv}
    {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
    {out1 out2 : Slice U8} {events : List CommitmentData}
    (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
    (hstep : step d s tx (.transact a proof extAmount fee out1 out2) = .ok (s', events))
    (hashes : HashesAgree d)
    (wf : WellFormed d s)
    (solana : PdasDoNotSign d tx.toTxContext) (hrentPos : tx.RentPositive)
    (crypto : NewNullifierAddressesDiffer d proof) (circuit : CircuitFacts d {proof})
    (rentFixed : tx.minimumBalance = some rent) :
    withSyscallSpec C in
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
  withSyscallSpec C
  exact transact_refines_between hstep hashes wf solana hrentPos crypto circuit rentFixed
    (fun hv => verifier_bridge d.crypto C laws proof hv a extAmount fee out1 out2) rfl

end

end Connection
