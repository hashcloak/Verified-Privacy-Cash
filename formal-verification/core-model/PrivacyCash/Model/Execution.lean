/-
Executions: what the chain can go through, starting before the program is
initialized.

Between (and within) transactions, two kinds of things happen to the chain:
  * the zkcash program runs one of its instructions (`step`), or
  * anything else happens (`EnvStep`): users transfer SOL, other programs
    create or change their own accounts, anyone sends lamports anywhere.
Solana's runtime limits what "anything else" can do to accounts this program
owns: only the owning program may change an account's data, reassign it, or
debit it. Everyone may credit it. `EnvStep` allows exactly that, and places
no restriction on other accounts except that nothing outside this program can
make an account hold this program's account types.

A transaction with several instructions is atomic, but a successful one is a
sequence of such steps and a failed one changes nothing, so single steps
cover every transaction. Instructions of this program reached through CPI
are `step`s with whatever signers the caller provides (`TxEnv.signers` is
arbitrary).
-/
import PrivacyCash.Model.Program
open Aeneas Aeneas.Std

namespace PrivacyCash.Model

/-- Whether data is one of this program's account types (only this program's
    instructions can create those). -/
def AccountData.isProgramData : AccountData → Bool
  | .treeAccount _ | .treeToken _ | .globalConfig _ | .nullifier _ => true
  | .empty | .foreign => false

/-- One step of the rest of the world: accounts this program owns keep their
    owner and data and can only gain lamports; any other account may change
    arbitrarily, except that it cannot come to hold this program's account
    types (that would take this program's signature for a PDA, or its code). -/
def EnvStep (programId : Pubkey) (s s' : State) : Prop :=
  ∀ k,
    ((s k).owner = programId →
      (s' k).owner = programId ∧ (s' k).data = (s k).data ∧
      (s k).lamports.val ≤ (s' k).lamports.val) ∧
    ((s k).owner ≠ programId → (s' k).data.isProgramData = false)

/-- A state before the program is initialized: it owns no account. -/
def Genesis (programId : Pubkey) (s : State) : Prop := ∀ k, (s k).owner ≠ programId

/-- One event of an execution. -/
inductive Event where
  /-- This program runs `ix` in transaction environment `tx`, emitting `emitted`. -/
  | program (tx : TxEnv) (ix : Instruction) (emitted : List CommitmentData)
  /-- The rest of the world acts (see `EnvStep`). -/
  | env

/-- `Run d s events s'`: starting from `s`, the events happen in order, each
    succeeding, and the chain ends in `s'`. (Failed instructions revert and
    change nothing, so they are simply left out of a run.) Keeping the events
    lets theorems state hypotheses about exactly the inputs a run used, such
    as collision-freedom of the nullifiers it spent. -/
inductive Run (d : Deployment) : State → List Event → State → Prop where
  | nil (s : State) : Run d s [] s
  | program {s s' s'' : State} {tx : TxEnv} {ix : Instruction} {emitted : List CommitmentData}
      {events : List Event} :
      step d s tx ix = .ok (s', emitted) → Run d s' events s'' →
        Run d s (.program tx ix emitted :: events) s''
  | env {s s' s'' : State} {events : List Event} :
      EnvStep d.programId s s' → Run d s' events s'' → Run d s (.env :: events) s''

/-- The states an execution can reach from a genesis state. -/
def Reachable (d : Deployment) (s : State) : Prop :=
  ∃ s₀ events, Genesis d.programId s₀ ∧ Run d s₀ events s

/-! ## Basic facts -/

/-- Runs compose: a run followed by a run is a run. -/
theorem Run.append {d : Deployment} {s₁ s₂ s₃ : State} {e₁ e₂ : List Event}
    (h₁ : Run d s₁ e₁ s₂) (h₂ : Run d s₂ e₂ s₃) : Run d s₁ (e₁ ++ e₂) s₃ := by
  induction h₁ with
  | nil => exact h₂
  | program hstep _ ih => exact .program hstep (ih h₂)
  | env henv _ ih => exact .env henv (ih h₂)

/-- The rest of the world never changes the data of an account this program owns. -/
theorem EnvStep.data_of_owned {programId : Pubkey} {s s' : State} (h : EnvStep programId s s') {k : Pubkey}
    (hk : (s k).owner = programId) : (s' k).owner = programId ∧ (s' k).data = (s k).data :=
  ⟨((h k).1 hk).1, ((h k).1 hk).2.1⟩

/-- Doing nothing is a step of the rest of the world (so `EnvStep` is not vacuous). -/
theorem EnvStep.refl_of_no_foreign_program_data (programId : Pubkey) (s : State)
    (h : ∀ k, (s k).owner ≠ programId → (s k).data.isProgramData = false) : EnvStep programId s s :=
  fun k => ⟨fun hk => ⟨hk, rfl, le_refl _⟩, h k⟩

end PrivacyCash.Model
