/-
Conformance: the model agrees with the compiled program.

The scenarios in `Tests/ConformanceTraces.lean` (generated; a fixed list covering each
Anchor check of each account, the arguments' boundary values and the `init`
funding paths, then 150 random ones from a fixed seed, then `transact`
deposits, withdrawals, double spends, fees, solvency thresholds and aliased
accounts with real Groth16 proofs) were run on
the real zkcash program (the mainnet build, `cargo build-sbf`, no features) in LiteSVM by
`formal-verification/conformance` (`scripts/check_conformance.sh` regenerates
them and fails if they changed). Each records the instruction's accounts
before, the instruction, and either the accounts after and the events emitted,
or how it failed. For every scenario, the `#guard` below runs the model's
`step` on the same accounts and instruction, with the program's real
addresses, bumps, rent and Poseidon empty-subtree roots, and checks it agrees:

  * success: every account of the instruction has the same lamports, owner
    and (decoded) data, and the same events were emitted, in order;
  * failure: the model fails the same way, as far as it distinguishes
    failures: Anchor rejecting an account, or the system program failing
    while Anchor creates an `init` account, is the model's `.accounts` (which
    Anchor check failed is not compared); an error the handler returns is the
    model's program error with the same code (`anchorErrorCode`).

This is evidence, not proof: it covers these scenarios only.
-/
import Tests.ConformanceTraces
open Aeneas Aeneas.Std PrivacyCash.Model

namespace PrivacyCash.Tests.Conformance

/-! ## Running the model on the scenarios -/

/-- The program's `zero_bytes` (light-hasher's Poseidon empty-subtree roots). -/
def zeroBytes : Std.Array (Std.Array U8 32#usize) 41#usize := arrayOf (b32 "") (zeroBytesList.map b32)

/-- An answer from a table, by input bytes. -/
def answer {α : Type} (table : List (String × α)) (input : List U8) : Option α :=
  (table.find? fun (i, _) => bytes i == input).map (·.2)

/-- An address no derivation in the trace produces. -/
def unknownAddress : Pubkey := pk (String.ofList (List.replicate 64 'f'))

/-- The mainnet deployment for a scenario, with the real values from the
    trace. A derivation the trace does not list gives `unknownAddress` / bump 0,
    and a Poseidon or SHA-256 call missing from the scenario's tables panics,
    so a model that strays from the program fails rather than passes. (A
    missing `alt_bn128` call answers "failed", which also makes verification
    fail.) -/
def deployment (t : Tables) : Deployment where
  programId := keyProgram
  createProgramAddress seeds := (addresses.lookup (seeds.map (·.val))).getD unknownAddress
  canonicalBump seeds := byte ((bumps.lookup (seeds.map (·.val))).getD 0)
  crypto :=
    { hasher :=
        { hash_pair := fun l r =>
            match (t.poseidon.find? fun (a, b, _) => bytes a == l.val && bytes b == r.val) with
            | some (_, _, o) => .ok (b32 o)
            | none => .fail .panic
          zero_bytes := .ok zeroBytes }
      sha256 :=
        { hash := fun data =>
            match answer t.sha data.val with
            | some o => .ok (b32 o)
            | none => .fail .panic }
      altBn128 :=
        ⟨fun i => (answer t.multiplication i.val).bind (·.map fun o => arrayOf (byte 255) (bytes o)),
         fun i => (answer t.addition i.val).bind (·.map fun o => arrayOf (byte 255) (bytes o)),
         fun i => (answer t.pairing i.val).bind (·.map b32)⟩ }
  adminPubkey := some keyAdmin

def txOf (sc : Scenario) : TxEnv :=
  { signers := sc.signers, minimumBalance := some fun n => u64 ((rent.lookup n).getD 0) }

def preState (sc : Scenario) : State :=
  sc.pre.foldl (fun s (k, a) => s.set k a) (fun _ => Account.default)

/-- Whether the model's outcome is the program's. -/
def agrees : Except PrivacyCash.Model.Error (State × List CommitmentData) → Expected → Bool
  | .ok (s, events), .ok post expected =>
    post.all (fun (k, a) => decide (s k = a)) && events == expected
  | .error .accounts, .accounts _ => true
  | .error .accounts, .system _ => true
  | .error (.transact .Runtime), .system _ => true
  | .error (.program e), .program c => anchorErrorCode e == c
  | .error (.transact (.Program e)), .program c => anchorErrorCode e == c
  | .error .unbalanced, .runtime r => r == "UnbalancedInstruction"
  | .error .panic, .runtime r => r == "ProgramFailedToComplete"
  | _, _ => false

/-- The scenarios where the model and the program disagree. -/
def mismatches : List String :=
  (scenarios.filter fun sc =>
    !agrees (step (deployment sc.crypto) (preState sc) (txOf sc) sc.ix) sc.expected).map
    (·.title)

#guard scenarios.length = 220
#guard mismatches = []

end PrivacyCash.Tests.Conformance
