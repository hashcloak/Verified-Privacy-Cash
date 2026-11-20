import Connection.CodeModelAssumptions
open Aeneas Aeneas.Std PrivacyCash.Model

/-! # Proofs: the code accepts `initialize` at most once in a code run

NOT FOR REVIEW: the claim is part of `IsRunOf.start` (`Connection/Mapping.lean`), which
`run_connection` concludes. An accepted `initialize` makes the program the owner of the tree's address. The program keeps
every account it owns (the Code Model's `Run.keepsOwned`). A later `initialize` needs that
address to be owned by the System Program (Anchor's `init`), which the program is not.
-/

namespace Connection

/-- Splits a code run at one of its steps: the steps before it form a code run to the state
    before it, the step itself is a step of the code, and the steps after it form a code run
    from the state after it. -/
theorem CodeRun.split {d : Deployment} {s₀ sₙ : State} {earlier later : List RunStep}
    {step : RunStep} (h : CodeRun d s₀ (earlier ++ step :: later) sₙ) :
    CodeRun d s₀ earlier step.before ∧ EventStep d step.before step.event step.after ∧
      CodeRun d step.after later sₙ := by
  induction earlier generalizing s₀ with
  | nil =>
    cases h with
    | cons he hrest => exact ⟨.nil _, he, hrest⟩
  | cons x earlier ih =>
    cases h with
    | cons he hrest =>
      obtain ⟨h1, h2, h3⟩ := ih hrest
      exact ⟨.cons he h1, h2, h3⟩

/-- Along a code run, the program keeps every account it owns (the Code Model's `Run.keepsOwned`,
    for `CodeRun`). -/
theorem CodeRun.keepsOwned {d : Deployment} {s s' : State} {steps : List RunStep}
    (h : CodeRun d s steps s') : KeepsOwned d.programId s s' := by
  induction h with
  | nil => exact KeepsOwned.refl _
  | @cons _ _ _ e _ he _ ih =>
    cases e with
    | program => exact (step_keepsOwned he.1).trans ih
    | env => exact he.keepsOwned.trans ih

/-- An accepted `initialize` needs the tree's address owned by the System Program before it,
    and leaves it owned by the program. -/
theorem initialize_treeOwner {d : Deployment} {s s' : State} {tx : TxEnv}
    {a : InitializeAccounts} {em : List CommitmentData}
    (h : step d s tx (.initialize a) = .ok (s', em)) :
    (s d.treeAddress).owner = systemProgram ∧ (s' d.treeAddress).owner = d.programId := by
  obtain ⟨s₄, hexec, hpure⟩ := PrivacyCash.Model.Except.bind_ok h
  obtain rfl : s₄ = s' := congrArg Prod.fst (Except.ok.inj hpure)
  replace h := hexec
  unfold execInitialize at h
  split at h
  · cases h
  rename_i hv
  have hvalid := not_not.mp hv
  have htA : a.treeAccount = d.treeAddress := hvalid.treeAccount.1
  refine ⟨htA ▸ hvalid.treeAccount.2.1, ?_⟩
  split at h
  · cases h
  split at h
  · cases h
  rename_i s₁ hs₁
  obtain ⟨s₀₂, h₀₂, h₃⟩ := Option.bind_eq_some_iff.mp hs₁
  obtain ⟨s₀₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h₀₂
  -- the first `init` gives the tree's address to the program; the rest keep it
  have own₁ : (s₁ d.treeAddress).owner = d.programId :=
    (KeepsOwned.initAccount h₂).trans (KeepsOwned.initAccount h₃) _
      (htA ▸ (initAccount_owner h₁))
  obtain ⟨r₀, -, h⟩ := PrivacyCash.Model.Except.bind_ok h
  cases r₀ with
  | Err e => cases h
  | Ok _ =>
    obtain ⟨⟨r, tree, token, config⟩, -, h⟩ := PrivacyCash.Model.Except.bind_ok h
    cases r with
    | Err e => cases h
    | Ok _ =>
      rw [PrivacyCash.Model.checkBalanced_ok h]
      exact ((KeepsOwned.setData _ _ _).trans
        ((KeepsOwned.setData _ _ _).trans (KeepsOwned.setData _ _ _))) _ own₁
where
  /-- `init` makes the program the owner of the new account. -/
  initAccount_owner {pid : Pubkey} {s s' : State} {mb : Nat → U64} {payer key : Pubkey}
      {space : Nat} {data : AccountData} (h : s.initAccount pid mb payer key space data = some s') :
      (s' key).owner = pid := by
    unfold State.initAccount at h
    obtain ⟨s₀, -, rfl⟩ := Option.map_eq_some_iff.mp h
    simp [State.set]

/-- After an accepted `initialize`, no later step of the code run is an `initialize`. -/
theorem initialize_at_most_once {d : Deployment} (notSystem : ProgramNotSystem d)
    {s₀ sₙ : State} {steps : List RunStep} (hrun : CodeRun d s₀ steps sₙ)
    {earlier later : List RunStep} {first : RunStep} (hsplit : steps = earlier ++ first :: later)
    {txEnv : TxEnv} {a : InitializeAccounts} (hfirst : first.IsInitialize txEnv a) :
    ∀ step ∈ later, ∀ txEnv' a', ¬ step.IsInitialize txEnv' a' := by
  intro step hmem txEnv' a' ⟨em', hstep⟩
  obtain ⟨em, hfirstEv⟩ := hfirst
  subst hsplit
  obtain ⟨-, hfe, hrest⟩ := CodeRun.split hrun
  rw [hfirstEv] at hfe
  have owned := (initialize_treeOwner hfe.1).2
  obtain ⟨middle, after, rfl⟩ := List.append_of_mem hmem
  obtain ⟨hmid, hse, -⟩ := CodeRun.split hrest
  rw [hstep] at hse
  have stillOwned := hmid.keepsOwned _ owned
  exact notSystem (stillOwned.symm.trans (initialize_treeOwner hse.1).1)

/-- An accepted `initialize` is the only one of the code run: no step before or after it is an
    `initialize`. A step before it would be an earlier `initialize` with this one after it. -/
theorem initialize_only_one {d : Deployment} (notSystem : ProgramNotSystem d)
    {s₀ sₙ : State} {steps : List RunStep} (hrun : CodeRun d s₀ steps sₙ)
    {earlier later : List RunStep} {first : RunStep} (hsplit : steps = earlier ++ first :: later)
    {txEnv : TxEnv} {a : InitializeAccounts} (hfirst : first.IsInitialize txEnv a) :
    ∀ step ∈ earlier ++ later, ∀ txEnv' a', ¬ step.IsInitialize txEnv' a' := by
  intro step hmem txEnv' a' hstep
  rcases List.mem_append.mp hmem with hmem | hmem
  · obtain ⟨before, between, rfl⟩ := List.append_of_mem hmem
    exact initialize_at_most_once notSystem hrun (later := between ++ first :: later)
      (by rw [hsplit, List.append_assoc, List.cons_append]) hstep first
      (List.mem_append_right _ List.mem_cons_self) txEnv a hfirst
  · exact initialize_at_most_once notSystem hrun hsplit hfirst step hmem txEnv' a' hstep

end Connection
