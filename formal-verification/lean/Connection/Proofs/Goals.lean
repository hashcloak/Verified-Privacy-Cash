import Connection.Proofs.Execution
import Connection.Proofs.StepComplete
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # The spec's goals of the code (not for review)

Proofs of the goals stated of the code in `Connection/CodeModelStatements.lean`, where the
statements are reviewed: each follows from a connection theorem's proof and the spec's theorem
for the same goal. -/

namespace Connection

/-! ## Goals about runs -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [AddCommGroup G2]
  [Module Spec.F G2] [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event} {states : List State}
  (hgen : Genesis d.programId s₀) (hrun : ExecutionPath d s₀ evs states s)
  (hpid : d.programId ≠ systemProgram) (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
  (laws : PairingLaws C.e) (hashes : HashesAgree d.crypto)
  (assume : ExecutionAssumptions d s₀ evs) (sameRent : ∀ tx ix em, .program tx ix em ∈ evs → SameRent rent tx)
  (hi : Initialized d s)
include hgen hrun hpid C laws hashes assume sameRent hi

theorem spends_are_genuine_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.SpendsAreGenuine r wit :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.spends_are_genuine params r

theorem no_double_spend_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.NoDoubleSpend r wit :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.no_double_spend params r

theorem pool_backs_notes_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.PoolBacksNotes params r wit :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.balance params r

theorem only_owner_spends_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.OnlyOwnerSpends r wit :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.honest_note_spent_only_with_owner_key params r

theorem only_authorities_change_config_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      Spec.Goals.OnlyAuthoritiesChangeConfig params r :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.only_authorities_change_config params r

theorem admin_powers_limited_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      Spec.Goals.AdminPowersLimited params r :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.admin_powers_limited params r

end

/-! ## Goals about one transaction -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [AddCommGroup G2]
  [Module Spec.F G2] [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s₀ s s' : State} {evs : List Event} {tx : TxEnv}
  {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
  {out1 out2 : Slice U8} {events : List CommitmentData}
  (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
  (hstep : Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s')
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
  (hashes : HashesAgree d.crypto) (solana : SolanaFacts d tx)
  (crypto : CryptoFacts d proof) (circuit : CircuitFacts d {proof}) (sameRent : SameRent rent tx)
include hgen hrun hpid hstep C laws hashes solana crypto circuit sameRent

theorem same_payout_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    ∀ (T : Spec.TxInputs), Spec.Goals.ExtDataWellFormed T → T.pubInputs = inputs.pubInputs →
      Spec.Goals.SamePayout T inputs :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  fun T hT hSame => Spec.Goals.same_public_inputs_same_external_data T hT _ _ _ hSame
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto circuit sameRent)

theorem only_signers_pay_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    Spec.Goals.OnlySignersPay inputs (toWorld d rent s)
      (toWorld d rent s') :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  Spec.Goals.only_signers_pay _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto circuit sameRent)

theorem exact_payouts_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof extAmount fee out1 out2
    Spec.Goals.ExactPayouts inputs (toWorld d rent s)
      (toWorld d rent s') :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  Spec.Goals.exact_payouts _ _ _
    (transact_connection_pf hgen hrun hpid hstep C laws hashes solana crypto circuit sameRent)

end

/-! ## Liveness: G3a and G3b -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [AddCommGroup G2]
  [Module Spec.F G2] [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
  (hgen : Genesis d.programId s₀) (hrun : Run d s₀ evs s) (hpid : d.programId ≠ systemProgram)
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
  (hashes : HashesAgree d.crypto) (assume : CompletenessAssumptions d.crypto C)
include hgen hrun hpid C laws hashes assume

theorem honest_spend_is_accepted_pf
    {tx : TxEnv} {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {ext : I64} {fee : U64}
    {out1 out2 : Slice U8} {tree : zkcash_core.merkle_tree.MerkleTreeAccount}
    {tt : zkcash_core.admin.TreeTokenAccount} {config : zkcash_core.admin.GlobalConfig}
    (reach : ReachesProgram d rent s tx a proof ext fee out1 out2 tree tt config)
    (notL1 : ext.val ≠ 0) (notA0 : proof.proof_a.val ≠ List.replicate 64 0#u8) :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    let inputs := toInputs tx.signers a proof ext fee out1 out2
    ∀ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params))
      (wit : ℕ → Spec.Witness) (witness : Spec.Witness) (k : ℕ),
      toWorld d rent s = r.final →
      r.WitnessesFor wit →
      Spec.HonestSpend r wit inputs witness k →
      Spec.LimitsNotHit r.final inputs →
      (∃ s' events, step d s tx (.transact a proof ext fee out1 out2) = .ok (s', events))
        ∨ Spec.SpendBlockedByBreak r wit inputs witness k :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  fun params r wit witness k hfinal hwit hH hL =>
    (Spec.Goals.honest_spend_is_accepted params r wit hwit _ witness k hH hL).imp_left
      (step_accepts_of_spec C laws hashes assume (wf_reachable hgen hrun hpid hashes) reach notL1
        notA0 _ hfinal)

theorem admins_cannot_lock_withdrawals_pf :
    letI : Spec.Groups := syscallGroups C
    letI : Spec.Pairing := syscallPairing C
    letI : Spec.Deployment := ⟨programKey C⟩
    ∀ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params))
      (wit : ℕ → Spec.Witness) (spentAmt : ℕ),
      toWorld d rent s = r.final →
      r.WitnessesFor wit →
      2 ≤ spentAmt →
      ∃ payout feeAmount : ℕ,
        Spec.Goals.WithdrawalWay r.final.state.config spentAmt payout feeAmount
        ∧ spentAmt / 2 ≤ payout
        ∧ ∀ (tx : TxEnv) (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (ext : I64)
            (fee : U64) (out1 out2 : Slice U8) (tree : zkcash_core.merkle_tree.MerkleTreeAccount)
            (tt : zkcash_core.admin.TreeTokenAccount) (config : zkcash_core.admin.GlobalConfig)
            (witness : Spec.Witness) (k : ℕ),
          ReachesProgram d rent s tx a proof ext fee out1 out2 tree tt config →
          proof.proof_a.val ≠ List.replicate 64 0#u8 →
          let inputs := toInputs tx.signers a proof ext fee out1 out2
          Spec.HonestSpend r wit inputs witness k →
          witness.inAmt 0 + witness.inAmt 1 = (spentAmt : Spec.F) →
          inputs.extAmt = -(payout : ℤ) → inputs.f = feeAmount →
          inputs.R ∈ Set.range r.final.state.tree.history →
          Spec.treeHasRoom r.final.state.tree →
          Spec.balancesFit inputs r.final →
          (∃ s' events, step d s tx (.transact a proof ext fee out1 out2) = .ok (s', events))
            ∨ Spec.SpendBlockedByBreak r wit inputs witness k :=
  letI := syscallGroups C; letI := syscallPairing C; letI : Spec.Deployment := ⟨programKey C⟩
  fun params r wit spentAmt hfinal hwit hSpentAmt =>
    let ⟨payout, feeAmount, hway, hhalf, haccept⟩ :=
      Spec.Goals.admins_cannot_lock_withdrawals params r wit hwit spentAmt hSpentAmt
    ⟨payout, feeAmount, hway, hhalf, fun _ _ _ ext _ _ _ _ _ _ witness k reach notA0 hH hV hA hF hW hR hB =>
      (haccept _ witness k hH hV hA hF hW hR hB).imp_left
        (step_accepts_of_spec C laws hashes assume (wf_reachable hgen hrun hpid hashes) reach
          (fun h0 => by
            have h1 := hway.1
            have h2 : (ext.val : ℤ) = -(payout : ℤ) := hA
            omega) notA0 _ hfinal)⟩

end

end Connection
