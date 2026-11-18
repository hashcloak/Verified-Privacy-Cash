import Connection.Proofs.Basic
open Aeneas Aeneas.Std PrivacyCash.Model

/-! # What the spec sees of an execution, step by step (not for review)

The bridge (`Execution.lean`) and completeness over runs (`RunComplete.lean`) build the spec run
event by event. `ExecutionView` is what they carry along: a fold over the execution. At the end,
`isRunOf_of_view` turns it into `IsRunOf` (`Mapping.lean`), which says the same by positions. -/

namespace Connection

/-- `isTransactEvent e`: event `e` is an accepted `transact`. -/
def isTransactEvent : Event → Bool
  | .program _ (.transact ..) _ => true
  | _ => false

/-- `transactPositions evs`: the positions of the accepted `transact`s, in order. The `j`-th is
    the spec run's transaction `j`. -/
def transactPositions (evs : List Event) : List ℕ :=
  (List.range evs.length).filter fun i => isTransactEvent (evs.getD i .env)

/-- `InitRecord`: what `initialize` set up: its authority, its transaction's signers, and the
    spec world it left. -/
structure InitRecord where
  initializer : Spec.Pubkey
  signers : List Spec.Pubkey
  world : Spec.World

/-- `ExecutionView`: what the spec sees of an execution so far.
    - `init`: what `initialize` set up, once it has run;
    - `closedGaps`: for each transaction so far, the admin changes since the one before it;
    - `openGap`: the admin changes since the last transaction;
    - `poolBeforeTx`: just before each transaction so far, the chain's pool balance;
    - `afterTx`: after each transaction so far, the chain's spec state and pool balance. -/
structure ExecutionView where
  init : Option InitRecord := none
  closedGaps : List (List Spec.AdminChange) := []
  openGap : List Spec.AdminChange := []
  poolBeforeTx : List ℕ := []
  afterTx : List (Spec.State × ℕ) := []

/-- `v.afterEvent d rent before e after`: the view `v` after event `e` took the chain from
    `before` to `after`. Outside actions change nothing the view records. -/
def ExecutionView.afterEvent (v : ExecutionView) (d : Deployment) (rent : Nat → U64)
    (before : State) (e : Event) (after : State) : ExecutionView :=
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

/-- `v.afterEvents d rent before evs states`: the view `v` after the events `evs`, from `before`
    through `states`. -/
def ExecutionView.afterEvents (d : Deployment) (rent : Nat → U64) :
    ExecutionView → State → List Event → List State → ExecutionView
  | v, before, e :: es, after :: states =>
    ExecutionView.afterEvents d rent (v.afterEvent d rent before e after) after es states
  | v, _, _, _ => v

/-- `executionView d rent s₀ evs states`: what the spec sees of the whole execution. -/
def executionView (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event)
    (states : List State) : ExecutionView :=
  ExecutionView.afterEvents d rent {} s₀ evs states

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

/-! ## The view, by positions -/

/-- An execution path records one state per event. -/
theorem ExecutionPath.length_eq {d : Deployment} {s s' : State} {evs : List Event}
    {states : List State} (h : ExecutionPath d s evs states s') : states.length = evs.length := by
  induction h with
  | nil => rfl
  | program _ _ _ ih => simp [ih]
  | env _ _ ih => simp [ih]

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

theorem getD_cons_default {t s s' : State} {ts : List State} {n : ℕ} (h : n ≤ ts.length) :
    (t :: ts).getD n s = (t :: ts).getD n s' := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simp; omega)]
  rfl

theorem stateAt_snoc {s₀ s' : State} {states : List State} {i : ℕ} (h : i ≤ states.length) :
    stateAt s₀ (states ++ [s']) i = stateAt s₀ states i := by
  unfold stateAt
  simp only [List.getD_eq_getElem?_getD]
  rw [← List.cons_append, List.getElem?_append_left (by simp; omega)]

theorem stateAt_snoc_last {s₀ s' : State} {states : List State} :
    stateAt s₀ (states ++ [s']) (states.length + 1) = s' := by
  unfold stateAt
  simp only [List.getD_eq_getElem?_getD]
  rw [← List.cons_append, List.getElem?_append_right (by simp)]
  simp

theorem afterEvents_snoc {d : Deployment} {rent : Nat → U64} (e : Event) (s' : State) :
    ∀ (evs : List Event) (v : ExecutionView) (s : State) (states : List State),
      states.length = evs.length →
      ExecutionView.afterEvents d rent v s (evs ++ [e]) (states ++ [s']) =
        (ExecutionView.afterEvents d rent v s evs states).afterEvent d rent
          (stateAt s states evs.length) e s' := by
  intro evs
  induction evs with
  | nil =>
    intro v s states h
    cases states with
    | nil => simp [ExecutionView.afterEvents, stateAt]
    | cons => simp at h
  | cons e₀ es ih =>
    intro v s states h
    cases states with
    | nil => simp at h
    | cons t ts =>
      simp only [List.cons_append, ExecutionView.afterEvents]
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      rw [ih _ _ _ h]
      congr 1
      unfold stateAt
      rw [List.length_cons, List.getD_cons_succ, getD_cons_default (h ▸ le_refl _)]

theorem lt_of_mem_transactPositions {evs : List Event} {i : ℕ} (h : i ∈ transactPositions evs) :
    i < evs.length :=
  List.mem_range.mp (List.mem_filter.mp h).1

theorem getD_snoc_left {evs : List Event} {e : Event} {k : ℕ} (hk : k < evs.length) :
    (evs ++ [e]).getD k .env = evs.getD k .env := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem getD_snoc_last {evs : List Event} {e : Event} : (evs ++ [e]).getD evs.length .env = e := by
  simp [List.getD_eq_getElem?_getD]

theorem transactPositions_snoc (evs : List Event) (e : Event) :
    transactPositions (evs ++ [e]) =
      transactPositions evs ++ (if isTransactEvent e then [evs.length] else []) := by
  unfold transactPositions
  rw [List.length_append, List.length_singleton, List.range_succ, List.filter_append]
  congr 1
  · apply List.filter_congr
    intro i hi
    rw [getD_snoc_left (List.mem_range.mp hi)]
  · rw [List.filter_cons, List.filter_nil, getD_snoc_last]

theorem adminChangesBefore_snoc {d : Deployment} {s₀ s' : State} {evs : List Event} {e : Event}
    {states : List State} (hlen : states.length = evs.length) {i : ℕ} (hi : i ≤ evs.length) :
    adminChangesBefore d s₀ (evs ++ [e]) (states ++ [s']) i = adminChangesBefore d s₀ evs states i := by
  unfold adminChangesBefore
  apply flatMap_congr_mem
  intro k hk
  have hk' : k < evs.length := by have := List.mem_range.mp hk; omega
  rw [getD_snoc_left hk', stateAt_snoc (by omega)]

theorem adminChangesBefore_snoc_env {d : Deployment} {s₀ s' : State} {evs : List Event}
    {states : List State} (hlen : states.length = evs.length) :
    adminChangesBefore d s₀ (evs ++ [.env]) (states ++ [s']) (evs.length + 1) =
      adminChangesBefore d s₀ evs states evs.length := by
  rw [← adminChangesBefore_snoc (e := .env) (s' := s') hlen le_rfl]
  unfold adminChangesBefore
  rw [List.range_succ, List.flatMap_append]
  simp

theorem adminChangesBefore_snoc_program {d : Deployment} {s₀ s' : State} {evs : List Event}
    {states : List State} (hlen : states.length = evs.length) (tx : TxEnv) (ix : Instruction)
    (em : List CommitmentData) :
    adminChangesBefore d s₀ (evs ++ [.program tx ix em]) (states ++ [s']) (evs.length + 1) =
      adminChangesBefore d s₀ evs states evs.length ++
        (toAdminChange d (stateAt s₀ states evs.length) tx ix).toList := by
  rw [← adminChangesBefore_snoc (e := .program tx ix em) (s' := s') hlen le_rfl]
  unfold adminChangesBefore
  rw [List.range_succ, List.flatMap_append]
  simp [stateAt_snoc (le_of_eq hlen.symm)]

theorem isInitializeAt_snoc {evs : List Event} {e : Event} {k : ℕ} {tx : TxEnv}
    {a : InitializeAccounts} :
    IsInitializeAt (evs ++ [e]) k tx a ↔
      IsInitializeAt evs k tx a ∨ (k = evs.length ∧ ∃ em, e = .program tx (.initialize a) em) := by
  unfold IsInitializeAt
  constructor
  · rintro ⟨em, h⟩
    rcases Nat.lt_or_ge k evs.length with hk | hk
    · rw [List.getElem?_append_left hk] at h; exact Or.inl ⟨em, h⟩
    · rw [List.getElem?_append_right hk] at h
      rcases Nat.eq_or_lt_of_le hk with rfl | hk'
      · simp at h; exact Or.inr ⟨rfl, em, h⟩
      · rw [List.getElem?_eq_none (by simp; omega)] at h; cases h
  · rintro (⟨em, h⟩ | ⟨rfl, em, rfl⟩)
    · exact ⟨em, by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]; exact h⟩
    · exact ⟨em, by simp⟩

theorem lt_of_isInitializeAt {evs : List Event} {k : ℕ} {tx : TxEnv} {a : InitializeAccounts}
    (h : IsInitializeAt evs k tx a) : k < evs.length := by
  obtain ⟨em, h⟩ := h
  exact (List.getElem?_eq_some_iff.mp h).1

/-- What the view records, by positions (the form `IsRunOf` uses). -/
structure ViewByPositions (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event)
    (states : List State) (v : ExecutionView) : Prop where
  poolBefore : v.poolBeforeTx =
    (transactPositions evs).map fun i => (stateAt s₀ states i).lamports d.poolAddress
  after : v.afterTx = (transactPositions evs).map fun i =>
    ((toWorld d rent (stateAt s₀ states (i+1))).state, (stateAt s₀ states (i+1)).lamports d.poolAddress)
  gapsLength : v.closedGaps.length = (transactPositions evs).length
  gaps : ∀ j i, (transactPositions evs)[j]? = some i →
    (v.closedGaps.take (j+1)).flatten = adminChangesBefore d s₀ evs states i
  all : v.closedGaps.flatten ++ v.openGap = adminChangesBefore d s₀ evs states evs.length
  init : ∀ rec, v.init = some rec → ∃ k tx a, IsInitializeAt evs k tx a ∧
    (∀ k' tx' a', IsInitializeAt evs k' tx' a' → k' ≤ k) ∧
    rec = ⟨toPubkey a.authority, tx.signers.map toPubkey, toWorld d rent (stateAt s₀ states (k+1))⟩

/-- Positions of the shorter execution keep their entries in a map after one more event. -/
theorem map_snoc_congr {β : Type} {evs : List Event} {states : List State} {s₀ s' : State}
    (hlen : states.length = evs.length) (f : State → State → β) :
    ((transactPositions evs).map fun i => f (stateAt s₀ (states ++ [s']) i)
        (stateAt s₀ (states ++ [s']) (i+1))) =
      (transactPositions evs).map fun i => f (stateAt s₀ states i) (stateAt s₀ states (i+1)) := by
  apply List.map_congr_left
  intro i hi
  have := lt_of_mem_transactPositions hi
  rw [stateAt_snoc (by omega), stateAt_snoc (by omega)]

theorem viewByPositions {d : Deployment} {rent : Nat → U64} {s₀ : State} :
    ∀ (evs : List Event) (states : List State), states.length = evs.length →
      ViewByPositions d rent s₀ evs states (executionView d rent s₀ evs states) := by
  intro evs
  induction evs using List.reverseRecOn with
  | nil =>
    intro states h
    cases states with
    | nil =>
      refine ⟨rfl, rfl, rfl, ?_, rfl, ?_⟩
      · intro j i h; simp [transactPositions] at h
      · intro rec h; cases h
    | cons => simp at h
  | append_singleton evs e ih =>
    intro states hlen
    rcases states.eq_nil_or_concat with rfl | ⟨ts, s', rfl⟩
    · simp at hlen
    rw [List.concat_eq_append] at hlen ⊢
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hlen
    have IH := ih ts hlen
    rw [show executionView d rent s₀ (evs ++ [e]) (ts ++ [s']) =
        (executionView d rent s₀ evs ts).afterEvent d rent (stateAt s₀ ts evs.length) e s' from
      afterEvents_snoc e s' evs {} s₀ ts hlen]
    -- positions of the shorter execution are below `evs.length`
    have pos_lt : ∀ j i, (transactPositions evs)[j]? = some i → i < evs.length := fun j i h =>
      lt_of_mem_transactPositions (List.mem_of_getElem? h)
    have adm_le : ∀ i, i ≤ evs.length → adminChangesBefore d s₀ (evs ++ [e]) (ts ++ [s']) i =
        adminChangesBefore d s₀ evs ts i := fun i hi => adminChangesBefore_snoc hlen hi
    have pb := map_snoc_congr (s₀ := s₀) (s' := s') hlen
      (fun a _ => a.lamports d.poolAddress)
    have af := map_snoc_congr (s₀ := s₀) (s' := s') hlen
      (fun _ b => ((toWorld d rent b).state, b.lamports d.poolAddress))
    try simp only at pb af
    have hlast : stateAt s₀ (ts ++ [s']) (evs.length + 1) = s' := hlen ▸ stateAt_snoc_last
    have hbefore : stateAt s₀ (ts ++ [s']) evs.length = stateAt s₀ ts evs.length :=
      stateAt_snoc (le_of_eq hlen.symm)
    -- an initialize recorded by the shorter view stays the last one, unless `e` is one
    have init_old : ∀ (noInit : ∀ tx a em, e ≠ .program tx (.initialize a) em) rec,
        (executionView d rent s₀ evs ts).init = some rec →
        ∃ k tx a, IsInitializeAt (evs ++ [e]) k tx a ∧
          (∀ k' tx' a', IsInitializeAt (evs ++ [e]) k' tx' a' → k' ≤ k) ∧
          rec = ⟨toPubkey a.authority, tx.signers.map toPubkey,
            toWorld d rent (stateAt s₀ (ts ++ [s']) (k+1))⟩ := by
      intro noInit rec hrec
      obtain ⟨k, tx, a, hk, hlast', rfl⟩ := IH.init rec hrec
      have hkl := lt_of_isInitializeAt hk
      refine ⟨k, tx, a, isInitializeAt_snoc.mpr (Or.inl hk), ?_, ?_⟩
      · intro k' tx' a' h'
        rcases isInitializeAt_snoc.mp h' with h' | ⟨-, em, he⟩
        · exact hlast' k' tx' a' h'
        · exact absurd he (noInit tx' a' em)
      · rw [stateAt_snoc (by omega)]
    cases e with
    | env =>
      -- an outside action: nothing recorded
      have htp : transactPositions (evs ++ [.env]) = transactPositions evs := by
        rw [transactPositions_snoc]; simp [isTransactEvent]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [ExecutionView.afterEvent]; rw [htp, pb]; exact IH.poolBefore
      · simp only [ExecutionView.afterEvent]; rw [htp, af]; exact IH.after
      · simp only [ExecutionView.afterEvent]; rw [htp]; exact IH.gapsLength
      · intro j i h
        rw [htp] at h
        simp only [ExecutionView.afterEvent]
        rw [IH.gaps j i h, adm_le i (le_of_lt (pos_lt j i h))]
      · simp only [ExecutionView.afterEvent, List.length_append, List.length_singleton]
        rw [adminChangesBefore_snoc_env hlen]; exact IH.all
      · intro rec h
        exact init_old (fun _ _ _ h => by cases h) rec (by simpa [ExecutionView.afterEvent] using h)
    | program tx ix em =>
      -- an admin instruction: its admin change joins the open gap
      have admin_case :
          (∀ (v : ExecutionView) (before after : State), v.afterEvent d rent before (.program tx ix em) after =
            { v with openGap := v.openGap ++ (toAdminChange d before tx ix).toList }) →
          isTransactEvent (.program tx ix em) = false → (∀ a, ix ≠ .initialize a) →
          ViewByPositions d rent s₀ (evs ++ [.program tx ix em]) (ts ++ [s'])
            ((executionView d rent s₀ evs ts).afterEvent d rent (stateAt s₀ ts evs.length)
              (.program tx ix em) s') := by
        intro hv hnt hni
        have htp : transactPositions (evs ++ [.program tx ix em]) = transactPositions evs := by
          rw [transactPositions_snoc, hnt]; simp
        rw [hv]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [htp, pb]; exact IH.poolBefore
        · rw [htp, af]; exact IH.after
        · rw [htp]; exact IH.gapsLength
        · intro j i h
          rw [htp] at h
          rw [IH.gaps j i h, adm_le i (le_of_lt (pos_lt j i h))]
        · rw [List.length_append, List.length_singleton, adminChangesBefore_snoc_program hlen,
            ← IH.all, List.append_assoc]
        · intro rec h
          exact init_old (fun tx' a' em' h => by injection h with _ h2; exact hni _ h2) rec h
      cases ix with
      | updateDepositLimit acc l => exact admin_case (fun _ _ _ => rfl) rfl (fun _ h => by cases h)
      | updateGlobalConfig acc dep wd mg =>
        exact admin_case (fun _ _ _ => rfl) rfl (fun _ h => by cases h)
      | «initialize» a =>
        have htp : transactPositions (evs ++ [.program tx (.initialize a) em]) =
            transactPositions evs := by
          rw [transactPositions_snoc]; simp [isTransactEvent]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [ExecutionView.afterEvent]; rw [htp, pb]; exact IH.poolBefore
        · simp only [ExecutionView.afterEvent]; rw [htp, af]; exact IH.after
        · simp only [ExecutionView.afterEvent]; rw [htp]; exact IH.gapsLength
        · intro j i h
          rw [htp] at h
          simp only [ExecutionView.afterEvent]
          rw [IH.gaps j i h, adm_le i (le_of_lt (pos_lt j i h))]
        · simp only [ExecutionView.afterEvent, List.length_append, List.length_singleton]
          rw [adminChangesBefore_snoc_program hlen]
          simp [toAdminChange, IH.all]
        · intro rec h
          simp only [ExecutionView.afterEvent, Option.some.injEq] at h
          subst h
          refine ⟨evs.length, tx, a, isInitializeAt_snoc.mpr (Or.inr ⟨rfl, em, rfl⟩), ?_, ?_⟩
          · intro k' tx' a' h'
            have := lt_of_isInitializeAt h'
            simp at this; omega
          · rw [hlast]
      | transact acc proof ext fee out1 out2 =>
        have htp : transactPositions (evs ++ [.program tx (.transact acc proof ext fee out1 out2) em]) =
            transactPositions evs ++ [evs.length] := by
          rw [transactPositions_snoc]; simp [isTransactEvent]
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [ExecutionView.afterEvent]
          rw [htp, List.map_append, pb, IH.poolBefore]; simp [hbefore]
        · simp only [ExecutionView.afterEvent]
          rw [htp, List.map_append, af, IH.after]; simp [hlast]
        · simp only [ExecutionView.afterEvent]
          rw [htp, List.length_append, List.length_append, IH.gapsLength]; rfl
        · intro j i h
          rw [htp] at h
          simp only [ExecutionView.afterEvent]
          rcases Nat.lt_or_ge j (transactPositions evs).length with hj | hj
          · rw [List.getElem?_append_left hj] at h
            rw [List.take_append_of_le_length (by rw [IH.gapsLength]; omega), IH.gaps j i h,
              adm_le i (le_of_lt (pos_lt j i h))]
          · rw [List.getElem?_append_right hj] at h
            have hj' : j = (transactPositions evs).length := by
              rcases Nat.eq_or_lt_of_le hj with h' | h'
              · exact h'.symm
              · rw [List.getElem?_eq_none (by simp; omega)] at h; cases h
            subst hj'
            simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at h
            subst h
            rw [← IH.gapsLength, List.take_of_length_le (by simp), List.flatten_append,
              List.flatten_singleton, IH.all, adm_le _ le_rfl]
        · simp only [ExecutionView.afterEvent, List.length_append, List.length_singleton]
          rw [adminChangesBefore_snoc_program hlen]
          simp [toAdminChange, IH.all]
        · intro rec h
          exact init_old (fun _ _ _ h => by cases h) rec (by simpa [ExecutionView.afterEvent] using h)

/-! ## Transaction records, by positions -/

theorem runTxs_append (e₁ e₂ : List Event) : runTxs (e₁ ++ e₂) = runTxs e₁ ++ runTxs e₂ := by
  induction e₁ with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | program tx ix em => simp [runTxs, ih]
    | env => simp [runTxs, ih]

/-- The record of event `i`: as in `executionTxRecords`. -/
def recordAt (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event)
    (states : List State) (i : ℕ) : List TxRecord :=
  match evs[i]? with
  | some (Event.program tx (.transact a proof ext fee out1 out2) _) =>
    [{ inputs := toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩
       poolBefore := (stateAt s₀ states i).lamports d.poolAddress
       stateAfter := (toWorld d rent (stateAt s₀ states (i+1))).state
       poolAfter := (stateAt s₀ states (i+1)).lamports d.poolAddress
       adminChangesBefore := adminChangesBefore d s₀ evs states i }]
  | _ => []

theorem executionTxRecords_eq (d : Deployment) (rent : Nat → U64) (s₀ : State)
    (evs : List Event) (states : List State) :
    executionTxRecords d rent s₀ evs states =
      (List.range evs.length).flatMap (recordAt d rent s₀ evs states) := rfl

/-- The inputs of event `i`, if it is an accepted `transact`. -/
def inputsAt (evs : List Event) (i : ℕ) : List Spec.TxInputs :=
  match evs[i]? with
  | some (Event.program tx (.transact a proof ext fee out1 out2) _) =>
    [toInputs ⟨⟨tx.signers⟩, a, ⟨proof, ext, fee, out1, out2⟩⟩]
  | _ => []

theorem recordAt_map_inputs (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event)
    (states : List State) (i : ℕ) :
    (recordAt d rent s₀ evs states i).map TxRecord.inputs = inputsAt evs i := by
  unfold recordAt inputsAt
  rcases evs[i]? with _ | ⟨tx, ix, em⟩ | _
  · rfl
  · cases ix <;> rfl
  · rfl

theorem inputsAt_runTxs (evs : List Event) :
    (List.range evs.length).flatMap (inputsAt evs) = runTxs evs := by
  induction evs using List.reverseRecOn with
  | nil => rfl
  | append_singleton evs e ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
      runTxs_append, ← ih]
    congr 1
    · apply flatMap_congr_mem
      intro i hi
      unfold inputsAt
      rw [List.getElem?_append_left (List.mem_range.mp hi)]
    · simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      unfold inputsAt
      rw [List.getElem?_append_right le_rfl, Nat.sub_self, List.getElem?_cons_zero]
      rcases e with ⟨tx, ix, em⟩ | _
      · cases ix <;> simp [runTxs, stepTxs]
      · rfl

theorem executionTxRecords_map_inputs (d : Deployment) (rent : Nat → U64) (s₀ : State)
    (evs : List Event) (states : List State) :
    (executionTxRecords d rent s₀ evs states).map TxRecord.inputs = runTxs evs := by
  rw [executionTxRecords_eq, List.map_flatMap, ← inputsAt_runTxs]
  exact flatMap_congr_mem fun i _ => recordAt_map_inputs d rent s₀ evs states i

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

theorem recordAt_of_not_transact {d : Deployment} {rent : Nat → U64} {s₀ : State}
    {evs : List Event} {states : List State} {i : ℕ}
    (h : isTransactEvent (evs.getD i .env) = false) : recordAt d rent s₀ evs states i = [] := by
  unfold recordAt
  rw [List.getD_eq_getElem?_getD] at h
  rcases he : evs[i]? with _ | ⟨tx, ix, em⟩ | _
  · rfl
  · rw [he] at h
    cases ix <;> first | rfl | simp [isTransactEvent] at h
  · rfl

theorem event_of_mem_transactPositions {evs : List Event} {i : ℕ}
    (h : i ∈ transactPositions evs) :
    ∃ tx a proof ext fee out1 out2 em,
      evs[i]? = some (.program tx (.transact a proof ext fee out1 out2) em) := by
  unfold transactPositions at h
  obtain ⟨hi, ht⟩ := List.mem_filter.mp h
  rw [List.getD_eq_getElem?_getD] at ht
  rcases he : evs[i]? with _ | ⟨tx, ix, em⟩ | _
  · rw [he] at ht; simp [isTransactEvent] at ht
  · rw [he] at ht
    cases ix with
    | transact a proof ext fee out1 out2 => exact ⟨tx, a, proof, ext, fee, out1, out2, em, rfl⟩
    | _ => simp [isTransactEvent] at ht
  · rw [he] at ht; simp [isTransactEvent] at ht

/-- A projection of the records, by positions. -/
theorem executionTxRecords_map {β : Type} {d : Deployment} {rent : Nat → U64} {s₀ : State}
    {evs : List Event} {states : List State} (g : TxRecord → β) (G : ℕ → β)
    (hG : ∀ i ∈ transactPositions evs, (recordAt d rent s₀ evs states i).map g = [G i]) :
    (executionTxRecords d rent s₀ evs states).map g = (transactPositions evs).map G := by
  rw [executionTxRecords_eq, ← flatMap_filter_of_nil _ (fun i => isTransactEvent (evs.getD i .env))
    _ (fun i _ hp => recordAt_of_not_transact hp)]
  change ((transactPositions evs).flatMap _).map g = _
  rw [List.map_flatMap, flatMap_congr_mem hG, flatMap_singleton_eq_map]

/-- The record at a `transact`'s position. -/
theorem recordAt_of_mem {d : Deployment} {rent : Nat → U64} {s₀ : State} {evs : List Event}
    {states : List State} {i : ℕ} (hi : i ∈ transactPositions evs) :
    ∃ x, recordAt d rent s₀ evs states i = [x] ∧
      x.poolBefore = (stateAt s₀ states i).lamports d.poolAddress ∧
      x.stateAfter = (toWorld d rent (stateAt s₀ states (i+1))).state ∧
      x.poolAfter = (stateAt s₀ states (i+1)).lamports d.poolAddress ∧
      x.adminChangesBefore = adminChangesBefore d s₀ evs states i := by
  obtain ⟨tx, a, proof, ext, fee, out1, out2, em, he⟩ := event_of_mem_transactPositions hi
  unfold recordAt
  rw [he]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩

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
structure RunMatchesView (d : Deployment) (rent : Nat → U64) (v : ExecutionView)
    (txs : List Spec.TxInputs) (s : State) (params : Spec.InitParams)
    (r : Spec.Run (Spec.initWorld params)) : Prop where
  /-- The deployment: `params` names this deployment's addresses, rents and admin key. -/
  deployment : RunOfDeployment d rent params
  /-- The start: `initialize` ran, and `r` starts from what it set up. -/
  start : ∃ i : InitRecord, v.init = some i ∧ StartsFromRecord params i
  /-- The transactions: `r`'s transactions are the execution's. -/
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
def IsRunOfView (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event)
    (states : List State) (s : State) (params : Spec.InitParams)
    (r : Spec.Run (Spec.initWorld params)) : Prop :=
  RunMatchesView d rent (executionView d rent s₀ evs states) (runTxs evs) s params r

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

/-- The view's form gives `IsRunOf`. -/
theorem isRunOf_of_view {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    {states : List State} {params : Spec.InitParams}
    {r : Spec.Run (Spec.initWorld params)} (hlen : states.length = evs.length)
    (h : IsRunOfView d rent s₀ evs states s params r) : IsRunOf d rent s₀ evs states s params r := by
  have P := viewByPositions (d := d) (rent := rent) (s₀ := s₀) evs states hlen
  obtain ⟨hdep, ⟨rec, hrec, hst⟩, htxs, hpbl, hpb, hafl, haf, hadl, had, b, hb, hbad, hbw⟩ := h
  set v := executionView d rent s₀ evs states
  -- `r`'s admin changes up to `m` are the view's first `m` gaps
  have upTo : ∀ m, m ≤ r.txs.length → r.adminChangesUpTo m = (v.closedGaps.take m).flatten :=
    fun m hm => (flatten_take_eq (fun i hi => had i (hadl ▸ hi)) m (hadl ▸ hm)).symm
  have hlenTp : (transactPositions evs).length = r.txs.length := by
    rw [← hpbl, P.poolBefore, List.length_map]
  have hafter : (transactPositions evs).map (fun i =>
      ((toWorld d rent (stateAt s₀ states (i+1))).state,
        (stateAt s₀ states (i+1)).lamports d.poolAddress)) =
      (List.range r.txs.length).map fun j => ((r.ws (j+1)).state, (r.ws (j+1)).poolBalance) :=
    P.after.symm.trans (eq_range_map hafl haf)
  refine ⟨hdep, ?_, ?_, ⟨b, hb, ?_, hbw⟩⟩
  · obtain ⟨k, tx, a, hk, hlast, rfl⟩ := P.init rec hrec
    exact ⟨k, tx, a, hk, hlast, ⟨hst.initializer, hst.signers, hst.config, hst.balances⟩⟩
  · apply txRecords_ext
    · rw [runTxRecords_map_inputs, executionTxRecords_map_inputs, htxs]
    · rw [runTxRecords_map_poolBefore, executionTxRecords_map _
        (fun i => (stateAt s₀ states i).lamports d.poolAddress)
        (fun i hi => by obtain ⟨x, hx, h1, -⟩ := recordAt_of_mem hi; rw [hx]; simp [h1]),
        ← P.poolBefore]
      exact (eq_range_map hpbl hpb).symm
    · rw [runTxRecords_map_stateAfter, executionTxRecords_map _
        (fun i => (toWorld d rent (stateAt s₀ states (i+1))).state)
        (fun i hi => by obtain ⟨x, hx, -, h2, -⟩ := recordAt_of_mem hi; rw [hx]; simp [h2])]
      have e := congrArg (List.map Prod.fst) hafter
      simp only [List.map_map, Function.comp_def] at e
      exact e.symm
    · rw [runTxRecords_map_poolAfter, executionTxRecords_map _
        (fun i => (stateAt s₀ states (i+1)).lamports d.poolAddress)
        (fun i hi => by obtain ⟨x, hx, -, -, h3, -⟩ := recordAt_of_mem hi; rw [hx]; simp [h3])]
      have e := congrArg (List.map Prod.snd) hafter
      simp only [List.map_map, Function.comp_def] at e
      exact e.symm
    · rw [runTxRecords_map_admin, executionTxRecords_map _
        (fun i => adminChangesBefore d s₀ evs states i)
        (fun i hi => by obtain ⟨x, hx, -, -, -, h4⟩ := recordAt_of_mem hi; rw [hx]; simp [h4])]
      symm
      apply eq_range_map (by rw [List.length_map, hlenTp])
      intro j hj
      have hj' : j < (transactPositions evs).length := hlenTp ▸ hj
      rw [List.getElem?_map, List.getElem?_eq_getElem hj', Option.map_some,
        ← P.gaps j _ (List.getElem?_eq_getElem hj'), ← upTo (j+1) hj]
  · rw [upTo _ le_rfl, ← hadl, List.take_length, hbad, P.all]

/-- `IsRunOf` fixes the run's transactions: the execution's. -/
theorem IsRunOf.txs {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    {states : List State} {params : Spec.InitParams}
    {r : Spec.Run (Spec.initWorld params)} (h : IsRunOf d rent s₀ evs states s params r) :
    r.txs = runTxs evs := by
  have e := congrArg (List.map TxRecord.inputs) h.transactions
  rwa [runTxRecords_map_inputs, executionTxRecords_map_inputs] at e

/-- `IsRunOf` gives transaction `j`'s record from the code's at its position `i`. -/
theorem IsRunOf.record {d : Deployment} {rent : Nat → U64} {s₀ s : State} {evs : List Event}
    {states : List State} {params : Spec.InitParams}
    {r : Spec.Run (Spec.initWorld params)} (h : IsRunOf d rent s₀ evs states s params r)
    {j i : ℕ} (hj : (transactPositions evs)[j]? = some i) :
    (r.updatedValues j).balances (toPubkey d.poolAddress) = (stateAt s₀ states i).lamports d.poolAddress ∧
    r.adminChangesUpTo (j+1) = adminChangesBefore d s₀ evs states i := by
  have hpb := congrArg (fun L => (L.map TxRecord.poolBefore)[j]?) h.transactions
  have had := congrArg (fun L => (L.map TxRecord.adminChangesBefore)[j]?) h.transactions
  rw [runTxRecords_map_poolBefore, executionTxRecords_map _
    (fun i => (stateAt s₀ states i).lamports d.poolAddress)
    (fun i hi => by obtain ⟨x, hx, h1, -⟩ := recordAt_of_mem hi; rw [hx]; simp [h1]),
    List.getElem?_map, List.getElem?_map, hj] at hpb
  rw [runTxRecords_map_admin, executionTxRecords_map _
    (fun i => adminChangesBefore d s₀ evs states i)
    (fun i hi => by obtain ⟨x, hx, -, -, -, h4⟩ := recordAt_of_mem hi; rw [hx]; simp [h4]),
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
