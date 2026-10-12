/-
No theorem of the model relies on an axiom beyond Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`): every assumption is a
hypothesis the theorem states. Checked for every theorem in the
`PrivacyCash`, `zkcash_core` and `core` namespaces at build time.
-/
import PrivacyCash
open Lean

namespace PrivacyCash.Tests.Axioms

def ours (n : Name) : Bool :=
  (`PrivacyCash).isPrefixOf n || (`zkcash_core).isPrefixOf n || (`core).isPrefixOf n

def standard (a : Name) : Bool :=
  a == ``propext || a == ``Classical.choice || a == ``Quot.sound

run_meta do
  let thms := (← getEnv).constants.fold (init := #[]) fun acc n c =>
    match c with
    | .thmInfo _ => if ours n then acc.push n else acc
    | _ => acc
  if thms.size < 100 then throwError "only {thms.size} theorems found: the audit is not looking"
  for t in thms do
    let axs ← collectAxioms t
    let extra := axs.filter fun a => !standard a
    unless extra.isEmpty do throwError "{t} relies on {extra}"

end PrivacyCash.Tests.Axioms
