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
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event} {states : List State}
  (hgen : Genesis d.programId s₀) (hrun : ExecutionPath d s₀ evs states s)
  (hpid : d.programId ≠ systemProgram) (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT)
  (laws : PairingLaws C.e) (hashes : HashesAgree d)
  (assume : ExecutionFacts d evs) (sameRent : ∀ tx ix em, .program tx ix em ∈ evs → SameRent rent tx.minimumBalance)
  (hi : Initialized d s)
include hgen hrun hpid C laws hashes assume sameRent hi

theorem spends_are_genuine_pf :
    withSyscallSpec C in
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.SpendsAreGenuine r wit :=
  withSyscallSpec C in
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.spends_are_genuine params r

theorem no_double_spend_pf :
    withSyscallSpec C in
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.NoDoubleSpend r wit :=
  withSyscallSpec C in
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.no_double_spend params r

theorem pool_backs_notes_pf :
    withSyscallSpec C in
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.PoolBacksNotes params r wit :=
  withSyscallSpec C in
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.balance params r

theorem only_owner_spends_pf :
    withSyscallSpec C in
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      ∀ wit, r.WitnessesFor wit → Spec.Goals.OnlyOwnerSpends r wit :=
  withSyscallSpec C in
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.honest_note_spent_only_with_owner_key params r

theorem only_authorities_change_config_pf :
    withSyscallSpec C in
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      Spec.Goals.OnlyAuthoritiesChangeConfig params r :=
  withSyscallSpec C in
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.only_authorities_change_config params r

theorem admin_powers_limited_pf :
    withSyscallSpec C in
    ∃ params r, IsRunOf d rent s₀ evs states s params r ∧
      Spec.Goals.AdminPowersLimited params r :=
  withSyscallSpec C in
  run_satisfies hgen hrun hpid C laws hashes assume sameRent hi _
    fun params r => Spec.Goals.admin_powers_limited params r

end

/-! ## Goals about one transaction -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s s' : State} {tx : TxEnv}
  {a : TransactAccounts} {proof : zkcash_core.transact.Proof} {extAmount : I64} {fee : U64}
  {out1 out2 : Slice U8} {events : List CommitmentData}
  (reachable : Reachable d s) (hpid : d.programId ≠ systemProgram)
  (hstep : Run d s [.program tx (.transact a proof extAmount fee out1 out2) events] s')
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
  (hashes : HashesAgree d) (solana : PdasDoNotSign d tx.toTxContext)
  (crypto : NewNullifierAddressesDiffer d proof) (circuit : CircuitFacts d {proof}) (sameRent : SameRent rent tx.minimumBalance)
include reachable hpid hstep C laws hashes solana crypto circuit sameRent

theorem same_payout_pf :
    withSyscallSpec C in
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩
    ∀ (T : Spec.TxInputs), Spec.Goals.ExtDataWellFormed T → T.pubInputs = inputs.pubInputs →
      Spec.Goals.SamePayout T inputs :=
  withSyscallSpec C in
  fun T hT hSame => Spec.Goals.same_public_inputs_same_external_data T hT _ _ _ hSame
    (transact_connection_pf reachable hpid hstep C laws hashes solana crypto circuit sameRent)

theorem only_signers_pay_pf :
    withSyscallSpec C in
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩
    Spec.Goals.OnlySignersPay inputs (toWorld d rent s)
      (toWorld d rent s') :=
  withSyscallSpec C in
  Spec.Goals.only_signers_pay _ _ _
    (transact_connection_pf reachable hpid hstep C laws hashes solana crypto circuit sameRent)

theorem exact_payouts_pf :
    withSyscallSpec C in
    let inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, extAmount, fee, out1, out2⟩⟩
    Spec.Goals.ExactPayouts inputs (toWorld d rent s)
      (toWorld d rent s') :=
  withSyscallSpec C in
  Spec.Goals.exact_payouts _ _ _
    (transact_connection_pf reachable hpid hstep C laws hashes solana crypto circuit sameRent)

end

/-! ## Liveness: G3a and G3b -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] [Spec.PoseidonHashes] [Spec.Sha]
variable {d : Deployment} {rent : Nat → U64} {s : State}
  (reachable : Reachable d s) (hpid : d.programId ≠ systemProgram)
  (C : AltBn128Contracts d.crypto.altBn128 G1 G2 GT) (laws : PairingLaws C.e)
  (hashes : HashesAgree d) (crypto : CryptoSucceeds d.crypto C) (runtime : RuntimeFacts rent)
include reachable hpid C laws hashes crypto runtime

theorem honest_spend_is_accepted_pf
    (pdas : PdasOnlyByProgram d s) (initialized : Initialized d s)
    {tx : TransactTx} {sysvarRent : Option (Nat → U64)}
    (reach : ReachesProgram d s tx.accounts tx.args.proof) (sameRent : SameRent rent sysvarRent)
    (notL1 : tx.args.extAmount.val ≠ 0) (notA0 : tx.args.proof.proof_a.val ≠ List.replicate 64 0#u8) :
    withSyscallSpec C in
    let inputs := toInputs tx
    ∀ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params))
      (wit : ℕ → Spec.Witness) (witness : Spec.Witness) (k : ℕ),
      toWorld d rent s = r.final →
      r.WitnessesFor wit →
      Spec.HonestSpend r wit inputs witness k →
      Spec.LimitsNotHit r.final inputs →
      Accepts d s (tx.env sysvarRent) tx.instruction
        ∨ Spec.SpendBlockedByBreak r wit inputs witness k ∨ AddressCollision d {tx.args.proof} :=
  withSyscallSpec C in
  fun params r wit witness k hfinal hwit hH hL => by
    by_cases hc : AddressCollision d {tx.args.proof}
    · exact Or.inr (Or.inr hc)
    exact ((Spec.Goals.honest_spend_is_accepted params r wit hwit _ witness k hH hL).imp_left
      fun hacc => transact_complete_pf reachable hpid C laws hashes crypto runtime pdas
        (transactDistinct_of_noCollision (Set.mem_singleton _) hc) sameRent reach.accounts
        reach.signerPlain initialized notL1 notA0 (by rw [hfinal]; exact hacc.1)).imp_right Or.inl

theorem admins_cannot_lock_withdrawals_pf
    (pdas : PdasOnlyByProgram d s) (initialized : Initialized d s) :
    withSyscallSpec C in
    ∀ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params))
      (wit : ℕ → Spec.Witness) (spentAmt : ℕ),
      toWorld d rent s = r.final →
      r.WitnessesFor wit →
      2 ≤ spentAmt →
      ∃ payout feeAmount : ℕ,
        Spec.Goals.WithdrawalWay r.final.state.config spentAmt payout feeAmount
        ∧ spentAmt / 2 ≤ payout
        ∧ ∀ (tx : TransactTx) (sysvarRent : Option (Nat → U64)) (witness : Spec.Witness) (k : ℕ),
          ReachesProgram d s tx.accounts tx.args.proof →
          SameRent rent sysvarRent →
          tx.args.proof.proof_a.val ≠ List.replicate 64 0#u8 →
          let inputs := toInputs tx
          Spec.HonestSpend r wit inputs witness k →
          witness.inAmt 0 + witness.inAmt 1 = (spentAmt : Spec.F) →
          inputs.extAmt = -(payout : ℤ) → inputs.f = feeAmount →
          inputs.R ∈ Set.range r.final.state.tree.history →
          Spec.treeHasRoom r.final.state.tree →
          Spec.balancesFit inputs r.final →
          Accepts d s (tx.env sysvarRent) tx.instruction
            ∨ Spec.SpendBlockedByBreak r wit inputs witness k ∨ AddressCollision d {tx.args.proof} :=
  withSyscallSpec C in
  fun params r wit spentAmt hfinal hwit hSpentAmt =>
    let ⟨payout, feeAmount, hway, hhalf, haccept⟩ :=
      Spec.Goals.admins_cannot_lock_withdrawals params r wit hwit spentAmt hSpentAmt
    ⟨payout, feeAmount, hway, hhalf, fun tx _ witness k reach sameRent notA0 hH hV hA hF hW hR hB => by
      by_cases hc : AddressCollision d {tx.args.proof}
      · exact Or.inr (Or.inr hc)
      exact ((haccept _ witness k hH hV hA hF hW hR hB).imp_left
        fun hacc => transact_complete_pf reachable hpid C laws hashes crypto runtime pdas
          (transactDistinct_of_noCollision (Set.mem_singleton _) hc) sameRent reach.accounts
          reach.signerPlain initialized
          (fun h0 => by
            have h1 := hway.1
            have h2 : (tx.args.extAmount.val : ℤ) = -(payout : ℤ) := hA
            omega) notA0 (by rw [hfinal]; exact hacc.1)).imp_right Or.inl⟩

end

end Connection
