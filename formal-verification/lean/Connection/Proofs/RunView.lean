import Connection.Proofs.Basic
import Connection.Proofs.InitializeOnce
open Aeneas Aeneas.Std PrivacyCash.Model

/-! # What the spec sees of a code run, step by step (not for review)

The bridge (`Run.lean`) and completeness over runs (`RunComplete.lean`) build the spec run
step by step. `RunView` is what they carry along: a fold over the code run's steps. At the end,
`isRunOf_of_view` turns it into `IsRunOf` (`Mapping.lean`), which says the same per step. -/

namespace Connection

/-- `isTransactEvent e`: event `e` is an accepted `transact`. -/
def isTransactEvent : Event → Bool
  | .program _ (.transact ..) _ => true
  | _ => false

/-- `transactSteps steps`: the steps of the accepted `transact`s, each with its position, in
    order. The `j`-th is the spec run's transaction `j`. -/
def transactSteps (steps : List RunStep) : List (RunStep × ℕ) :=
  steps.zipIdx.filter fun p => isTransactEvent p.1.event

/-- `InitRecord`: what `initialize` set up: its authority, its transaction's signers, and the
    spec world it left. -/
structure InitRecord where
  initializer : Spec.Pubkey
  signers : List Spec.Pubkey
  world : Spec.World

/-- `RunView`: what the spec sees of a code run so far.
    - `init`: what `initialize` set up, once it has run;
    - `closedGaps`: for each transaction so far, the admin changes since the one before it;
    - `openGap`: the admin changes since the last transaction;
    - `poolBeforeTx`: just before each transaction so far, the chain's pool balance;
    - `afterTx`: after each transaction so far, the chain's spec state and pool balance. -/
structure RunView where
  init : Option InitRecord := none
  closedGaps : List (List Spec.AdminChange) := []
  openGap : List Spec.AdminChange := []
  poolBeforeTx : List ℕ := []
  afterTx : List (Spec.State × ℕ) := []

/-- `v.afterEvent d rent before e after`: the view `v` after event `e` took the chain from
    `before` to `after`. Outside actions change nothing the view records. -/
def RunView.afterEvent (v : RunView) (d : Deployment) (rent : Nat → U64)
    (before : State) (e : Event) (after : State) : RunView :=
  match e with
  | .env => v
  | .program tx ix _ =>
    match ix with
    | .initialize a =>
      { v with init := some ⟨toPubkey a.authority, tx.signers.map toPubkey,
          toWorld d rent after⟩ }
    | .transact .. =>
      { v with
        closedGaps := v.closedGaps ++ [v.openGap]
        openGap := []
        poolBeforeTx := v.poolBeforeTx ++ [before.lamports d.poolAddress]
        afterTx := v.afterTx ++ [((toWorld d rent after).state,
          after.lamports d.poolAddress)] }
    | _ => { v with openGap := v.openGap ++ (toAdminChange d before tx ix).toList }

/-- `v.afterSteps d rent steps`: the view `v` after the steps `steps`. -/
def RunView.afterSteps (d : Deployment) (rent : Nat → U64) (v : RunView)
    (steps : List RunStep) : RunView :=
  steps.foldl (fun w step => w.afterEvent d rent step.before step.event step.after) v

/-- `runView d rent steps`: what the spec sees of the whole code run. -/
def runView (d : Deployment) (rent : Nat → U64) (steps : List RunStep) : RunView :=
  RunView.afterSteps d rent {} steps

/-- `StartsFromRecord params i`: the spec run's start is what `initialize` set up (`i`). -/
structure StartsFromRecord (params : Spec.InitParams) (i : InitRecord) : Prop where
  /-- The initializer is the authority `initialize` named. -/
  initializer : params.initializer = i.initializer
  /-- The signers are those of `initialize`'s transaction. -/
  signers : params.signers = i.signers
  /-- The config is the one `initialize` wrote. -/
  config : params.cfg = i.world.state.config
  /-- Every account starts with its balance right after `initialize`, except the three it
      creates, whose balances (their rents) `initWorld` sets itself. -/
  balances : ∀ x ∉ ({params.pool, params.treeAccount, params.configAccount} : Set Spec.Pubkey),
    params.balances x = i.world.balances x

/-! ## The view, step by step -/

theorem afterSteps_append (d : Deployment) (rent : Nat → U64) (v : RunView)
    (steps₁ steps₂ : List RunStep) :
    RunView.afterSteps d rent v (steps₁ ++ steps₂) =
      RunView.afterSteps d rent (RunView.afterSteps d rent v steps₁) steps₂ :=
  List.foldl_append

theorem runView_snoc (d : Deployment) (rent : Nat → U64) (steps : List RunStep) (x : RunStep) :
    runView d rent (steps ++ [x]) =
      (runView d rent steps).afterEvent d rent x.before x.event x.after := by
  simp [runView, RunView.afterSteps]

theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- The first `m` lists of `L`, flattened, when `L`'s entries are `g 0, g 1, …`. -/
theorem flatten_take_eq {α : Type} {L : List (List α)} {g : ℕ → List α}
    (h : ∀ i (_ : i < L.length), L[i]? = some (g i)) :
    ∀ m, m ≤ L.length → (L.take m).flatten = (List.range m).flatMap g := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    rw [List.take_add_one, List.flatten_append, ih (by omega), List.range_succ, List.flatMap_append,
      h m (by omega)]
    simp

theorem eventsOf_append (steps₁ steps₂ : List RunStep) :
    eventsOf (steps₁ ++ steps₂) = eventsOf steps₁ ++ eventsOf steps₂ :=
  List.map_append

theorem adminChanges_append (d : Deployment) (steps₁ steps₂ : List RunStep) :
    adminChanges d (steps₁ ++ steps₂) = adminChanges d steps₁ ++ adminChanges d steps₂ :=
  List.flatMap_append

theorem transactSteps_snoc (steps : List RunStep) (x : RunStep) :
    transactSteps (steps ++ [x]) =
      transactSteps steps ++ (if isTransactEvent x.event then [(x, steps.length)] else []) := by
  unfold transactSteps
  rw [List.zipIdx_append, List.filter_append, Nat.zero_add, List.zipIdx_singleton]
  congr 1
  simp only [List.filter_cons, List.filter_nil]

theorem lt_of_mem_transactSteps {steps : List RunStep} {p : RunStep × ℕ}
    (h : p ∈ transactSteps steps) : p.2 < steps.length := by
  have := List.snd_lt_of_mem_zipIdx (List.mem_filter.mp h).1
  omega

/-- What the view records, per step (the form `IsRunOf` uses). -/
structure ViewBySteps (d : Deployment) (rent : Nat → U64) (steps : List RunStep) (v : RunView) :
    Prop where
  poolBefore : v.poolBeforeTx =
    (transactSteps steps).map fun p => p.1.before.lamports d.poolAddress
  after : v.afterTx = (transactSteps steps).map fun p =>
    ((toWorld d rent p.1.after).state, p.1.after.lamports d.poolAddress)
  gapsLength : v.closedGaps.length = (transactSteps steps).length
  gaps : ∀ j (p : RunStep × ℕ), (transactSteps steps)[j]? = some p →
    (v.closedGaps.take (j+1)).flatten = adminChanges d (steps.take p.2)
  all : v.closedGaps.flatten ++ v.openGap = adminChanges d steps
  init : ∀ rec, v.init = some rec → ∃ earlier step later tx a,
    steps = earlier ++ step :: later ∧
    step.IsInitialize tx a ∧ (∀ step' ∈ later, ∀ tx' a', ¬ step'.IsInitialize tx' a') ∧
    rec = ⟨toPubkey a.authority, tx.signers.map toPubkey, toWorld d rent step.after⟩

theorem viewBySteps {d : Deployment} {rent : Nat → U64} :
    ∀ steps : List RunStep, ViewBySteps d rent steps (runView d rent steps) := by
  intro steps
  induction steps using List.reverseRecOn with
  | nil =>
    refine ⟨rfl, rfl, rfl, ?_, rfl, ?_⟩
    · intro j p h; simp [transactSteps] at h
    · intro rec h; cases h
  | append_singleton steps x IH =>
    rw [runView_snoc]
    -- the earlier steps keep their positions and admin changes
    have pos_lt : ∀ j (p : RunStep × ℕ), (transactSteps steps)[j]? = some p →
        p.2 < steps.length :=
      fun j p h => lt_of_mem_transactSteps (List.mem_of_getElem? h)
    have take_le : ∀ i, i ≤ steps.length → (steps ++ [x]).take i = steps.take i :=
      fun i hi => List.take_append_of_le_length hi
    have gaps_old : ∀ (v : RunView), v.closedGaps = (runView d rent steps).closedGaps →
        ∀ j (p : RunStep × ℕ), (transactSteps steps)[j]? = some p →
          (v.closedGaps.take (j+1)).flatten = adminChanges d ((steps ++ [x]).take p.2) := by
      intro v hv j p h
      rw [hv, IH.gaps j p h, take_le _ (le_of_lt (pos_lt j p h))]
    -- an initialize recorded by the shorter view stays the last one, unless `x` is one
    have init_old : (∀ tx a, ¬ x.IsInitialize tx a) → ∀ rec,
        (runView d rent steps).init = some rec →
        ∃ earlier step later tx a, steps ++ [x] = earlier ++ step :: later ∧
          step.IsInitialize tx a ∧ (∀ step' ∈ later, ∀ tx' a', ¬ step'.IsInitialize tx' a') ∧
          rec = ⟨toPubkey a.authority, tx.signers.map toPubkey, toWorld d rent step.after⟩ := by
      intro noInit rec hrec
      obtain ⟨e, st, l, tx, a, hsplit, hst, hl, rfl⟩ := IH.init rec hrec
      refine ⟨e, st, l ++ [x], tx, a, by rw [hsplit]; simp, hst, ?_, rfl⟩
      intro st' hst' tx' a'
      rcases List.mem_append.mp hst' with h | h
      · exact hl st' h tx' a'
      · rw [List.mem_singleton] at h; subst h; exact noInit tx' a'
    obtain ⟨b, e, s'⟩ := x
    cases e with
    | env =>
      -- an outside action: nothing recorded
      have htp : transactSteps (steps ++ [⟨b, .env, s'⟩]) = transactSteps steps := by
        rw [transactSteps_snoc]; simp [isTransactEvent]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [htp]; exact IH.poolBefore
      · rw [htp]; exact IH.after
      · rw [htp]; exact IH.gapsLength
      · rw [htp]; exact gaps_old _ rfl
      · simp only [RunView.afterEvent]; rw [adminChanges_append]; simpa [adminChanges] using IH.all
      · exact init_old (fun _ _ ⟨_, h⟩ => by cases h)
    | program tx ix em =>
      -- an admin instruction: its admin change joins the open gap
      have admin_case :
          (∀ (v : RunView), v.afterEvent d rent b (.program tx ix em) s' =
            { v with openGap := v.openGap ++ (toAdminChange d b tx ix).toList }) →
          isTransactEvent (.program tx ix em) = false → (∀ a, ix ≠ .initialize a) →
          ViewBySteps d rent (steps ++ [⟨b, .program tx ix em, s'⟩])
            ((runView d rent steps).afterEvent d rent b (.program tx ix em) s') := by
        intro hv hnt hni
        have htp :
            transactSteps (steps ++ [⟨b, .program tx ix em, s'⟩]) = transactSteps steps := by
          rw [transactSteps_snoc]; simp [hnt]
        rw [hv]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [htp]; exact IH.poolBefore
        · rw [htp]; exact IH.after
        · rw [htp]; exact IH.gapsLength
        · rw [htp]; exact gaps_old _ rfl
        · rw [adminChanges_append, ← IH.all, List.append_assoc]; simp [adminChanges]
        · exact init_old (fun tx' a' ⟨em', h⟩ => by injection h with _ h2; exact hni _ h2)
      cases ix with
      | updateDepositLimit acc l => exact admin_case (fun _ => rfl) rfl (fun _ h => by cases h)
      | updateGlobalConfig acc dep wd mg =>
        exact admin_case (fun _ => rfl) rfl (fun _ h => by cases h)
      | «initialize» a =>
        have htp : transactSteps (steps ++ [⟨b, .program tx (.initialize a) em, s'⟩]) =
            transactSteps steps := by
          rw [transactSteps_snoc]; simp [isTransactEvent]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [htp]; exact IH.poolBefore
        · rw [htp]; exact IH.after
        · rw [htp]; exact IH.gapsLength
        · rw [htp]; exact gaps_old _ rfl
        · simp only [RunView.afterEvent]; rw [adminChanges_append]
          simpa [adminChanges, toAdminChange] using IH.all
        · intro rec h
          simp only [RunView.afterEvent, Option.some.injEq] at h
          subst h
          exact ⟨steps, _, [], tx, a, rfl, ⟨em, rfl⟩, by simp, rfl⟩
      | transact acc proof ext fee out1 out2 =>
        have htp := transactSteps_snoc steps
          ⟨b, .program tx (.transact acc proof ext fee out1 out2) em, s'⟩
        simp only [isTransactEvent, if_true] at htp
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [RunView.afterEvent]
          rw [htp, List.map_append, IH.poolBefore]; rfl
        · simp only [RunView.afterEvent]
          rw [htp, List.map_append, IH.after]; rfl
        · simp only [RunView.afterEvent]
          rw [htp, List.length_append, List.length_append, IH.gapsLength]; rfl
        · intro j p h
          rw [htp] at h
          simp only [RunView.afterEvent]
          rcases Nat.lt_or_ge j (transactSteps steps).length with hj | hj
          · rw [List.getElem?_append_left hj] at h
            rw [List.take_append_of_le_length (by rw [IH.gapsLength]; omega)]
            exact gaps_old _ rfl j p h
          · rw [List.getElem?_append_right hj] at h
            have hj' : j = (transactSteps steps).length := by
              rcases Nat.eq_or_lt_of_le hj with h' | h'
              · exact h'.symm
              · rw [List.getElem?_eq_none (by simp; omega)] at h; cases h
            subst hj'
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
            subst h
            rw [← IH.gapsLength, List.take_of_length_le (by simp), List.flatten_append,
              List.flatten_singleton, IH.all, take_le _ le_rfl, List.take_length]
        · simp only [RunView.afterEvent]
          rw [adminChanges_append, List.flatten_append, List.flatten_singleton, List.append_nil,
            IH.all]
          simp [adminChanges, toAdminChange]
        · intro rec h
          exact init_old (fun _ _ ⟨_, h⟩ => by cases h) rec (by simpa [RunView.afterEvent] using h)

/-! ## Transaction records, per step -/

theorem runTxs_append (e₁ e₂ : List Event) : runTxs (e₁ ++ e₂) = runTxs e₁ ++ runTxs e₂ := by
  induction e₁ with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | program tx ix em => simp [runTxs, ih]
    | env => simp [runTxs, ih]

/-- The record of step `p.1` at position `p.2`: as in `codeRunTxRecords`. -/
def recordOf (d : Deployment) (rent : Nat → U64) (steps : List RunStep) :
    RunStep × ℕ → List TxRecord
  | (step, i) =>
    match step.event with
    | .program tx (.transact a proof ext fee out1 out2) _ =>
      [{ inputs := toInputs ⟨tx.toTxContext, a, ⟨proof, ext, fee, out1, out2⟩⟩
         poolBefore := step.before.lamports d.poolAddress
         stateAfter := (toWorld d rent step.after).state
         poolAfter := step.after.lamports d.poolAddress
         adminChangesBefore := adminChanges d (steps.take i) }]
    | _ => []

theorem codeRunTxRecords_eq (d : Deployment) (rent : Nat → U64) (steps : List RunStep) :
    codeRunTxRecords d rent steps = steps.zipIdx.flatMap (recordOf d rent steps) := rfl

/-- The spec transactions of event `e`: those of `runTxs`. -/
def eventTxs : Event → List Spec.TxInputs
  | .program tx ix _ => stepTxs tx ix
  | .env => []

theorem runTxs_eventsOf (steps : List RunStep) :
    runTxs (eventsOf steps) = steps.flatMap fun step => eventTxs step.event := by
  induction steps with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨b, e, a⟩
    have ih' : runTxs (xs.map RunStep.event) = xs.flatMap fun step => eventTxs step.event := ih
    cases e <;> simp [eventsOf, runTxs, eventTxs, ih']

theorem recordOf_map_inputs (d : Deployment) (rent : Nat → U64) (steps : List RunStep)
    (p : RunStep × ℕ) : (recordOf d rent steps p).map TxRecord.inputs = eventTxs p.1.event := by
  rcases p with ⟨⟨b, e, a⟩, i⟩
  rcases e with ⟨tx, ix, em⟩ | _
  · cases ix <;> rfl
  · rfl

theorem codeRunTxRecords_map_inputs (d : Deployment) (rent : Nat → U64) (steps : List RunStep) :
    (codeRunTxRecords d rent steps).map TxRecord.inputs = runTxs (eventsOf steps) := by
  rw [codeRunTxRecords_eq, List.map_flatMap, runTxs_eventsOf,
    flatMap_congr_mem fun p _ => recordOf_map_inputs d rent steps p]
  conv_rhs => rw [← List.zipIdx_map_fst 0 steps]
  rw [List.flatMap_map]

theorem flatMap_filter_of_nil {α β : Type} (l : List α) (p : α → Bool) (f : α → List β)
    (h : ∀ x ∈ l, p x = false → f x = []) : (l.filter p).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have ih' := ih (fun y hy => h y (by simp [hy]))
    cases hx : p x
    · simp [hx, ih', h x (by simp) hx]
    · simp [hx, ih']

theorem flatMap_singleton_eq_map {α β : Type} (l : List α) (G : α → β) :
    l.flatMap (fun x => [G x]) = l.map G := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem recordOf_of_not_transact {d : Deployment} {rent : Nat → U64} {steps : List RunStep}
    {p : RunStep × ℕ} (h : isTransactEvent p.1.event = false) :
    recordOf d rent steps p = [] := by
  rcases p with ⟨⟨b, e, a⟩, i⟩
  rcases e with ⟨tx, ix, em⟩ | _
  · cases ix <;> first | rfl | simp [isTransactEvent] at h
  · rfl

/-- A projection of the records, per `transact` step. -/
theorem codeRunTxRecords_map {β : Type} {d : Deployment} {rent : Nat → U64}
    {steps : List RunStep} (g : TxRecord → β) (G : RunStep × ℕ → β)
    (hG : ∀ p ∈ transactSteps steps, (recordOf d rent steps p).map g = [G p]) :
    (codeRunTxRecords d rent steps).map g = (transactSteps steps).map G := by
  rw [codeRunTxRecords_eq, ← flatMap_filter_of_nil _ (fun p => isTransactEvent p.1.event)
    _ (fun p _ hp => recordOf_of_not_transact hp)]
  change ((transactSteps steps).flatMap _).map g = _
  rw [List.map_flatMap, flatMap_congr_mem hG, flatMap_singleton_eq_map]

/-- The record of a `transact` step. -/
theorem recordOf_of_mem {d : Deployment} {rent : Nat → U64} {steps : List RunStep}
    {p : RunStep × ℕ} (hp : p ∈ transactSteps steps) :
    ∃ x, recordOf d rent steps p = [x] ∧
      x.poolBefore = p.1.before.lamports d.poolAddress ∧
      x.stateAfter = (toWorld d rent p.1.after).state ∧
      x.poolAfter = p.1.after.lamports d.poolAddress ∧
      x.adminChangesBefore = adminChanges d (steps.take p.2) := by
  have ht := (List.mem_filter.mp hp).2
  rcases p with ⟨⟨b, e, a⟩, i⟩
  rcases e with ⟨tx, ix, em⟩ | _
  · cases ix with
    | transact => exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
    | _ => simp [isTransactEvent] at ht
  · simp [isTransactEvent] at ht

/-- Two lists of records are equal when each field agrees. -/
theorem txRecords_ext : ∀ {L M : List TxRecord},
    L.map TxRecord.inputs = M.map TxRecord.inputs →
    L.map TxRecord.poolBefore = M.map TxRecord.poolBefore →
    L.map TxRecord.stateAfter = M.map TxRecord.stateAfter →
    L.map TxRecord.poolAfter = M.map TxRecord.poolAfter →
    L.map TxRecord.adminChangesBefore = M.map TxRecord.adminChangesBefore → L = M
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _, _ => by simp at h
  | _ :: _, [], h, _, _, _, _ => by simp at h
  | x :: xs, y :: ys, h1, h2, h3, h4, h5 => by
    simp only [List.map_cons, List.cons.injEq] at h1 h2 h3 h4 h5
    rw [txRecords_ext h1.2 h2.2 h3.2 h4.2 h5.2]
    cases x; cases y
    simp_all

/-- A list given entry by entry is a map over its indices. -/
theorem eq_range_map {β : Type} {L : List β} {n : ℕ} {f : ℕ → β} (hl : L.length = n)
    (h : ∀ j (_ : j < n), L[j]? = some (f j)) : L = (List.range n).map f := by
  apply List.ext_getElem?
  intro j
  rcases Nat.lt_or_ge j n with hj | hj
  · rw [h j hj]; simp [hj]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

section
variable [Spec.PoseidonHashes] [Spec.Sha] [Spec.Groups] [AddCommGroup Spec.G1]
  [Module Spec.F Spec.G1]
  [CommGroup Spec.GT] [Spec.Pairing] [Spec.Deployment]

/-- `RunMatchesView d rent v txs s params r`: the spec run `r` is what the view `v` records,
    with transactions `txs`, ending at the code state `s`. -/
structure RunMatchesView (d : Deployment) (rent : Nat → U64) (v : RunView)
    (txs : List Spec.TxInputs) (s : State) (params : Spec.InitParams)
    (r : Spec.Run (Spec.initWorld params)) : Prop where
  /-- The deployment: `params` names this deployment's addresses, rents and admin key. -/
  deployment : RunOfDeployment d rent params
  /-- The start: `initialize` ran, and `r` starts from what it set up. -/
  start : ∃ i : InitRecord, v.init = some i ∧ StartsFromRecord params i
  /-- The transactions: `r`'s transactions are the code run's. -/
  txs : r.txs = txs
  /-- The pool before each transaction: `r` has the chain's pool balance, so `r.donated` is what
      the chain received. -/
  poolBeforeLength : v.poolBeforeTx.length = r.txs.length
  poolBefore : ∀ j (_ : j < r.txs.length),
    v.poolBeforeTx[j]? = some ((r.updatedValues j).balances (toPubkey d.poolAddress))
  /-- After each transaction, `r` has the chain's tree, nullifier accounts, pool address, config
      and pool balance. Other balances may differ: `r` takes them from the spec's `transact`; the
      next allowed change starts from the chain's. -/
  afterLength : v.afterTx.length = r.txs.length
  after : ∀ j (_ : j < r.txs.length),
    v.afterTx[j]? = some ((r.ws (j+1)).state, (r.ws (j+1)).poolBalance)
  /-- Before each transaction, `r` records exactly the admin instructions since the previous
      one, with their transactions' signers. -/
  adminLength : v.closedGaps.length = r.txs.length
  admin : ∀ j (_ : j < r.txs.length), v.closedGaps[j]? = some (r.updatedValues j).adminChanges
  /-- `s` is `r`'s final world after an allowed change recording the admin instructions since
      the last transaction. -/
  final : ∃ b : Spec.UpdatedValuesBetweenTransacts, b.Allowed r.final ∧
    b.adminChanges = v.openGap ∧ toWorld d rent s = r.final.withUpdatedValues b

/-- The view's form of `IsRunOf`. -/
def IsRunOfView (d : Deployment) (rent : Nat → U64) (steps : List RunStep) (s : State)
    (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params)) : Prop :=
  RunMatchesView d rent (runView d rent steps) (runTxs (eventsOf steps)) s params r

theorem runTxRecords_map_inputs {w₀ : Spec.World} (r : Spec.Run w₀) (pool : Spec.Pubkey) :
    (runTxRecords r pool).map TxRecord.inputs = r.txs :=
  List.ext_getElem (by simp [runTxRecords]) (fun j _ _ => by simp [runTxRecords])

theorem runTxRecords_map_poolBefore {w₀ : Spec.World} (r : Spec.Run w₀)
    (pool : Spec.Pubkey) : (runTxRecords r pool).map TxRecord.poolBefore =
      (List.range r.txs.length).map fun j => (r.updatedValues j).balances pool :=
  List.ext_getElem (by simp [runTxRecords]) (fun j _ _ => by simp [runTxRecords])

theorem runTxRecords_map_stateAfter {w₀ : Spec.World} (r : Spec.Run w₀)
    (pool : Spec.Pubkey) : (runTxRecords r pool).map TxRecord.stateAfter =
      (List.range r.txs.length).map fun j => (r.ws (j+1)).state :=
  List.ext_getElem (by simp [runTxRecords]) (fun j _ _ => by simp [runTxRecords])

theorem runTxRecords_map_poolAfter {w₀ : Spec.World} (r : Spec.Run w₀)
    (pool : Spec.Pubkey) : (runTxRecords r pool).map TxRecord.poolAfter =
      (List.range r.txs.length).map fun j => (r.ws (j+1)).poolBalance :=
  List.ext_getElem (by simp [runTxRecords]) (fun j _ _ => by simp [runTxRecords])

theorem runTxRecords_map_admin {w₀ : Spec.World} (r : Spec.Run w₀)
    (pool : Spec.Pubkey) : (runTxRecords r pool).map TxRecord.adminChangesBefore =
      (List.range r.txs.length).map fun j => r.adminChangesUpTo (j+1) :=
  List.ext_getElem (by simp [runTxRecords]) (fun j _ _ => by simp [runTxRecords])

/-- The view's form gives `IsRunOf`, for a code run (its `initialize` is the only one). -/
theorem isRunOf_of_view {d : Deployment} {rent : Nat → U64} {s₀ s : State}
    {steps : List RunStep} {params : Spec.InitParams} {r : Spec.Run (Spec.initWorld params)}
    (notSystem : ProgramNotSystem d) (hrun : CodeRun d s₀ steps s)
    (h : IsRunOfView d rent steps s params r) : IsRunOf d rent steps s params r := by
  have P := viewBySteps (d := d) (rent := rent) steps
  obtain ⟨hdep, ⟨rec, hrec, hst⟩, htxs, hpbl, hpb, hafl, haf, hadl, had, b, hb, hbad, hbw⟩ := h
  set v := runView d rent steps
  -- `r`'s admin changes up to `m` are the view's first `m` gaps
  have upTo : ∀ m, m ≤ r.txs.length → r.adminChangesUpTo m = (v.closedGaps.take m).flatten :=
    fun m hm => (flatten_take_eq (fun i hi => had i (hadl ▸ hi)) m (hadl ▸ hm)).symm
  have hlenTp : (transactSteps steps).length = r.txs.length := by
    rw [← hpbl, P.poolBefore, List.length_map]
  have hafter : (transactSteps steps).map (fun p =>
      ((toWorld d rent p.1.after).state, p.1.after.lamports d.poolAddress)) =
      (List.range r.txs.length).map fun j => ((r.ws (j+1)).state, (r.ws (j+1)).poolBalance) :=
    P.after.symm.trans (eq_range_map hafl haf)
  refine ⟨hdep, ?_, ?_, ⟨b, hb, ?_, hbw⟩⟩
  · obtain ⟨e, st, l, tx, a, hsplit, hst', -, rfl⟩ := P.init rec hrec
    exact ⟨e, st, l, tx, a, hsplit, hst',
      ⟨hst.initializer, hst.signers, hst.config, hst.balances⟩,
      initialize_only_one notSystem hrun hsplit hst'⟩
  · apply txRecords_ext
    · rw [runTxRecords_map_inputs, codeRunTxRecords_map_inputs, htxs]
    · rw [runTxRecords_map_poolBefore, codeRunTxRecords_map _
        (fun p => p.1.before.lamports d.poolAddress)
        (fun p hp => by obtain ⟨x, hx, h1, -⟩ := recordOf_of_mem hp; rw [hx]; simp [h1]),
        ← P.poolBefore]
      exact (eq_range_map hpbl hpb).symm
    · rw [runTxRecords_map_stateAfter, codeRunTxRecords_map _
        (fun p => (toWorld d rent p.1.after).state)
        (fun p hp => by obtain ⟨x, hx, -, h2, -⟩ := recordOf_of_mem hp; rw [hx]; simp [h2])]
      have e := congrArg (List.map Prod.fst) hafter
      simp only [List.map_map, Function.comp_def] at e
      exact e.symm
    · rw [runTxRecords_map_poolAfter, codeRunTxRecords_map _
        (fun p => p.1.after.lamports d.poolAddress)
        (fun p hp => by obtain ⟨x, hx, -, -, h3, -⟩ := recordOf_of_mem hp; rw [hx]; simp [h3])]
      have e := congrArg (List.map Prod.snd) hafter
      simp only [List.map_map, Function.comp_def] at e
      exact e.symm
    · rw [runTxRecords_map_admin, codeRunTxRecords_map _
        (fun p => adminChanges d (steps.take p.2))
        (fun p hp => by obtain ⟨x, hx, -, -, -, h4⟩ := recordOf_of_mem hp; rw [hx]; simp [h4])]
      symm
      apply eq_range_map (by rw [List.length_map, hlenTp])
      intro j hj
      have hj' : j < (transactSteps steps).length := hlenTp ▸ hj
      rw [List.getElem?_map, List.getElem?_eq_getElem hj', Option.map_some,
        ← P.gaps j _ (List.getElem?_eq_getElem hj'), ← upTo (j+1) hj]
  · rw [upTo _ le_rfl, ← hadl, List.take_length, hbad, P.all]

/-- `IsRunOf` fixes the run's transactions: the code run's. -/
theorem IsRunOf.txs {d : Deployment} {rent : Nat → U64} {s : State} {steps : List RunStep}
    {params : Spec.InitParams} {r : Spec.Run (Spec.initWorld params)}
    (h : IsRunOf d rent steps s params r) : r.txs = runTxs (eventsOf steps) := by
  have e := congrArg (List.map TxRecord.inputs) h.transactions
  rwa [runTxRecords_map_inputs, codeRunTxRecords_map_inputs] at e

/-- `IsRunOf` gives transaction `j`'s record from the code's `transact` step `p`. -/
theorem IsRunOf.record {d : Deployment} {rent : Nat → U64} {s : State} {steps : List RunStep}
    {params : Spec.InitParams} {r : Spec.Run (Spec.initWorld params)}
    (h : IsRunOf d rent steps s params r) {j : ℕ} {p : RunStep × ℕ}
    (hj : (transactSteps steps)[j]? = some p) :
    (r.updatedValues j).balances (toPubkey d.poolAddress) = p.1.before.lamports d.poolAddress ∧
    r.adminChangesUpTo (j+1) = adminChanges d (steps.take p.2) := by
  have hpb := congrArg (fun L => (L.map TxRecord.poolBefore)[j]?) h.transactions
  have had := congrArg (fun L => (L.map TxRecord.adminChangesBefore)[j]?) h.transactions
  rw [runTxRecords_map_poolBefore, codeRunTxRecords_map _
    (fun p => p.1.before.lamports d.poolAddress)
    (fun p hp => by obtain ⟨x, hx, h1, -⟩ := recordOf_of_mem hp; rw [hx]; simp [h1]),
    List.getElem?_map, List.getElem?_map, hj] at hpb
  rw [runTxRecords_map_admin, codeRunTxRecords_map _
    (fun p => adminChanges d (steps.take p.2))
    (fun p hp => by obtain ⟨x, hx, -, -, -, h4⟩ := recordOf_of_mem hp; rw [hx]; simp [h4]),
    List.getElem?_map, List.getElem?_map, hj] at had
  simp at hpb had
  obtain ⟨a, ha, e1⟩ := hpb
  obtain ⟨a', ha', e2⟩ := had
  rw [List.getElem?_eq_some_iff] at ha ha'
  obtain ⟨_, rfl⟩ := ha
  obtain ⟨_, rfl⟩ := ha'
  simp only [List.getElem_range] at e1 e2
  exact ⟨e1, e2⟩
end

end Connection
