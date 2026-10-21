import Connection.Proofs.Transact
import PrivacyCash.Proofs.Groth16
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Proofs: the verifier bridge

NOT FOR REVIEW: the statements are restated in `Connection/Statements.lean`.

The program's verifier (extracted `verify_proof` with the extracted key, on the `alt_bn128`
syscalls) accepts only proofs that satisfy the spec's `Groth16.verify`, once the spec's groups,
pairing and key are the syscalls' groups, the syscall pairing and the program's key. -/

namespace Connection
open PrivacyCash.Proofs.Groth16 (ic vkxOf programVerifier_groth16)

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] {s : AltBn128}

/-- **The bridge.** If the program's verifier accepts `proof`, the spec's `proofValid` holds for
    the mapped transaction, with the spec instantiated by the syscalls and the program's key. -/
theorem verifier_bridge (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT)
    (laws : PairingLaws C.e) (proof : zkcash_core.transact.Proof)
    (h : c.proofVerifier.verify proof = ok true)
    (a : TransactAccounts) (ext : I64) (fee : U64) (out1 out2 : Slice U8) :
    letI : LeanSpec.Groups := syscallGroups G1 G2 GT
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    LeanSpec.proofValid (toInputs a proof ext fee out1 out2 (proofPoints C proof)) := by
  obtain ⟨-, -, A, Cp, α, B, β, γ, δ, d1, d2, d3, d4, d5, d6, d7, heq⟩ :=
    programVerifier_groth16 c C proof h
  letI : LeanSpec.Groups := syscallGroups G1 G2 GT
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  -- the decoded points
  have hA : (C.decodeG1 proof.proof_a).getD 0 = A := by rw [d1]; rfl
  have hB : (C.decodeG2 proof.proof_b).getD 0 = B := by rw [d2]; rfl
  have hC : (C.decodeG1 proof.proof_c).getD 0 = Cp := by rw [d3]; rfl
  have hα : (C.decodeG1 zkcash_core.verifying_key.VERIFYING_KEY.vk_alpha_g1).getD 0 = α := by rw [d4]; rfl
  have hβ : (C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_beta_g2).getD 0 = β := by rw [d5]; rfl
  have hγ : (C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_gamme_g2).getD 0 = γ := by rw [d6]; rfl
  have hδ : (C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_delta_g2).getD 0 = δ := by rw [d7]; rfl
  -- the spec's vk_x is the code's
  have hvec : ∀ i : Fin 7, LeanSpec.Groth16.toVector (toInputs a proof ext fee out1 out2 (proofPoints C proof)).pubInputs i
      = toF ((publicInputs proof)[i.val]!) := by
    intro i; fin_cases i <;> rfl
  have hsmul : ∀ (b : Std.Array U8 32#usize) (P : G1), toF b • P = beNatOf b • P := by
    intro b P
    show ((beNat b : ℕ) : LeanSpec.F) • P = _
    rw [Nat.cast_smul_eq_nsmul]; rfl
  have hvkx : ic C zkcash_core.verifying_key.VERIFYING_KEY 0 +
      ∑ i : Fin 7, LeanSpec.Groth16.toVector (toInputs a proof ext fee out1 out2 (proofPoints C proof)).pubInputs i •
        ic C zkcash_core.verifying_key.VERIFYING_KEY i.succ.val
      = vkxOf C zkcash_core.verifying_key.VERIFYING_KEY proof := by
    simp only [vkxOf, hvec, hsmul, Fin.val_succ]
    rw [Fin.sum_univ_eq_sum_range (fun j => beNatOf ((publicInputs proof)[j]!) •
      ic C zkcash_core.verifying_key.VERIFYING_KEY (j + 1)) 7]
  -- the equation
  show C.e ((C.decodeG1 proof.proof_a).getD 0) ((C.decodeG2 proof.proof_b).getD 0)
    = C.e ((C.decodeG1 zkcash_core.verifying_key.VERIFYING_KEY.vk_alpha_g1).getD 0)
        ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_beta_g2).getD 0) *
      C.e (ic C zkcash_core.verifying_key.VERIFYING_KEY 0 +
        ∑ i : Fin 7, LeanSpec.Groth16.toVector (toInputs a proof ext fee out1 out2 (proofPoints C proof)).pubInputs i •
          ic C zkcash_core.verifying_key.VERIFYING_KEY i.succ.val)
        ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_gamme_g2).getD 0) *
      C.e ((C.decodeG1 proof.proof_c).getD 0) ((C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_delta_g2).getD 0)
  rw [hA, hB, hC, hα, hβ, hγ, hδ, hvkx]
  rw [laws.neg_left] at heq
  have : (C.e A B)⁻¹ * (C.e (vkxOf C zkcash_core.verifying_key.VERIFYING_KEY proof) γ * C.e Cp δ * C.e α β) = 1 := by
    rw [← heq]; simp only [mul_assoc]
  have h2 := inv_mul_eq_one.mp this
  rw [h2]
  ac_rfl

/-- `transact_refines` with the verifier bridge in place of the temporary `hProofValid`. -/
theorem transact_refines_verified [LeanSpec.PoseidonHashes] [LeanSpec.Sha]
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
    letI : LeanSpec.Groups := syscallGroups G1 G2 GT
    letI : LeanSpec.Pairing := syscallPairing C laws
    letI : LeanSpec.Deployment := ⟨programKey C⟩
    let inputs := toInputs a proof extAmount fee out1 out2 (proofPoints C proof)
    let spent' := spent ∪ {inputs.k0, inputs.k1}
    LeanSpec.transact inputs (toWorld d rent spent s) (toWorld d rent spent' s') ∧
      WellFormed d spent' s' := by
  letI : LeanSpec.Groups := syscallGroups G1 G2 GT
  letI : LeanSpec.Pairing := syscallPairing C laws
  letI : LeanSpec.Deployment := ⟨programKey C⟩
  exact transact_refines (proofPoints C proof) hstep hashes wf solana crypto outside
    (fun hv => verifier_bridge d.crypto C laws proof hv a extAmount fee out1 out2)

end

end Connection
