import Connection.Proofs.ToySpend
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # A toy execution with an outside action: a donation to the pool (not for review)

Genesis, `initialize`, an outside action (`EnvStep`) that sends 1 lamport to the pool, then the
deposit of 2 lamports of `Connection/Proofs/ToyRun.lean` (from a pool holding 2 lamports instead
of 1). Every hypothesis of `run_connection` holds, and every spec run of the execution counts the
lamport as donated: `r.donated = 1` (`toy_donation_nonvacuous`). So the `.env` case of
`run_connection` is exercised, from `EnvStep` to the spec's `poolGains` and `Run.donated`. -/

namespace Connection.Toy
open zkcash_core
attribute [local instance] toyPoseidon toySpecSha toySpecGroups toySpecG1Group toySpecG2Group
  toySpecG1Module toySpecG2Module toySpecGTGroup toySpecPairing toySpecDeployment

/-- **A donation is an outside action**: from a state where the pool holds 1 lamport and no
    account outside the program holds program data, raising the pool to 2 lamports is an
    `EnvStep`. -/
theorem toy_donation_env {s₁ : State} {token : admin.TreeTokenAccount}
    (hK : s₁ tokenA = ⟨1#u64, toyD.programId, .treeToken token⟩)
    (hnp : ∀ k, (s₁ k).owner ≠ toyD.programId → (s₁ k).data.isProgramData = false) :
    EnvStep toyD.programId s₁ (s₁.set tokenA ⟨2#u64, toyD.programId, .treeToken token⟩) := by
  intro k
  by_cases hk : k = tokenA
  · subst hk
    rw [State.set_same, hK]
    exact ⟨fun _ => ⟨rfl, rfl, by simp⟩, fun h => absurd rfl h⟩
  · rw [State.set_other _ _ hk]
    exact ⟨fun h => ⟨h, rfl, le_refl _⟩, hnp k⟩

/-- **The hypotheses of `run_connection` hold with a donation inside the run.** The execution
    `initialize`, a donation of 1 lamport to the pool, deposit satisfies every hypothesis of
    `run_connection`, and every spec run of it counts 1 lamport as donated. -/
theorem toy_donation_nonvacuous :
    ∃ (s₀ s : State) (evs : List Event) (states : List State),
      Genesis toyD.programId s₀ ∧ ExecutionPath toyD s₀ evs states s ∧ DeploymentFacts toyD ∧
      PairingLaws toyC.e ∧ HashesAgree toyD.crypto ∧ ExecutionAssumptions toyD s₀ evs ∧
      ExecutionOutsideSpecDetail toyD toyRent s₀ evs ∧ Event.env ∈ evs ∧
      ∀ params r, IsRunOf toyD toyRent s₀ evs states s params r → r.donated = 1 := by
  obtain ⟨s₁, tree, token, config, hinit, hT, hK, hC, hP, hO, hshape, hroots, hsubs, hT0, hTn, hTb, hTm,
    hkb, hcb, hdr, hwr, hmr⟩ := toy_init_ok
  have hpid : toyD.programId ≠ systemProgram := by unfold toyD; decide +kernel
  obtain ⟨-, g2, -, g4, -, g6, -⟩ := addr_facts
  have h1 : step toyD toyS0 toyTx (.initialize toyInitA) = .ok (s₁, []) := by
    show (do let s' ← execInitialize toyD toyS0 toyTx toyInitA; pure (s', [])) = _
    rw [hinit]; rfl
  -- the donation
  have hnp : ∀ k, (s₁ k).owner ≠ toyD.programId → (s₁ k).data.isProgramData = false := by
    intro k hk
    by_cases e1 : k = treeA
    · subst e1; rw [hT] at hk; exact absurd rfl hk
    by_cases e2 : k = tokenA
    · subst e2; rw [hK] at hk; exact absurd rfl hk
    by_cases e3 : k = configA
    · subst e3; rw [hC] at hk; exact absurd rfl hk
    by_cases e4 : k = pk 1#u8
    · subst e4; rw [hP]; rfl
    rw [hO k e1 e2 e3 e4]; unfold toyS0; rw [if_neg e4]; rfl
  set s₁d := s₁.set tokenA ⟨2#u64, toyD.programId, .treeToken token⟩ with hs₁d
  have henv : EnvStep toyD.programId s₁ s₁d := toy_donation_env hK hnp
  -- the deposit, from the state after the donation
  have hO₁ : ∀ k, k ≠ treeA → k ≠ tokenA → k ≠ configA → k ≠ pk 1#u8 → s₁d k = toyS0 k :=
    fun k e1 e2 e3 e4 => by rw [hs₁d, State.set_other _ _ e2]; exact hO k e1 e2 e3 e4
  obtain ⟨s₂, e₂, -, h2, -⟩ := toy_deposit_ok_pool s₁d tree token config 2#u64 4#u64 (by simp) (by simp)
    (by rw [hs₁d, State.set_other _ _ g4]; exact hT)
    (by rw [hs₁d, State.set_same])
    (by rw [hs₁d, State.set_other _ _ (Ne.symm g6)]; exact hC)
    (by rw [hs₁d, State.set_other _ _ (Ne.symm g2)]; exact hP) hO₁
    hshape hroots hsubs hT0 hTn hTb (hTm ▸ default_limit_ge2) hkb hcb hdr hwr hmr
  -- the facts the deposit needs, from the toy deposit after `initialize`
  obtain ⟨-, -, -, -, -, -, -, -, solana, depCrypto, -⟩ := toy_execution
  refine ⟨toyS0, s₂, _, _, toyGenesis, .program h1 toyTx_rentPositive (.env henv (.program h2 toyTx_rentPositive (.nil _))), toyDeploymentFacts, toyLaws,
    toyHashesAgree, ⟨toy_fixed_addresses, ?_⟩, ⟨?_⟩, by simp, ?_⟩
  · intro pre post s tx ix em hsplit _
    rcases toy_split3 hsplit with hev | hev | hev <;> cases hev
    · trivial
    · exact ⟨solana, depCrypto⟩
  · intro pre post s tx ix em hsplit _
    rcases toy_split3 hsplit with hev | hev | hev <;> cases hev <;> rfl
  · intro params r hr
    obtain ⟨hpool, hrent, -, -, -, -, hpl, hpb, -⟩ := hr
    -- the spec sees the pool's balance before the deposit: 2 lamports
    have hv : (executionView toyD toyRent toyS0 [.program toyTx (.initialize toyInitA) [], .env,
        .program toyTx (.transact depA depProof 2#i64 0#u64 emptySlice emptySlice) e₂]
        [s₁, s₁d, s₂]).poolBeforeTx = [publicBalance s₁d (poolAddr toyD)] := rfl
    have hb : publicBalance s₁d (poolAddr toyD) = 2 := by
      unfold publicBalance
      rw [show poolAddr toyD = tokenA from rfl, hs₁d, State.set_same]; rfl
    rw [hv, hb] at hpl hpb
    have hlen : r.txs.length = 1 := hpl.symm
    have h0 := hpb 0 (by rw [hlen]; exact Nat.one_pos)
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h0
    -- the spec's start world has the pool at its rent, 1 lamport
    unfold LeanSpec.Run.donated LeanSpec.Run.donations
    rw [hlen, Finset.sum_range_one, r.start]
    simp only [LeanSpec.World.poolBalance, LeanSpec.initWorld, Function.update_self]
    rw [← hpool] at h0
    rw [← h0, hrent]; rfl

end Connection.Toy
