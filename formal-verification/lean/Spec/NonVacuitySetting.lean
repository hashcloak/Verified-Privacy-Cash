import Spec.Spec
import Mathlib.Algebra.Group.PUnit

/-! # Non-vacuity: the toy setting (for review)

The hash functions, groups, pairing and key that the non-vacuity statements
(`Spec/NonVacuityStatements.lean`) are about. All are deliberately broken, not cryptography:
`H2` is constant, `G1 = G2 = F`, `GT = Unit`, every pairing is `1`, a byte string decodes to
its length, and the key is all zeros. The proofs are in `Spec/NonVacuityProofs.lean`. -/
namespace LeanSpec.NonVacuity
open LeanSpec

/-- Toy hashes. `H2` is constant, so every Merkle path reaches the root `1`; `H3` is linear,
    so the nullifiers below differ. -/
@[reducible] def toyHashes : PoseidonHashes where
  H1 := fun a => a
  H2 := fun _ _ => 1
  H3 := fun a b c => a + 2 * b + 3 * c
  H4 := fun a b c d => a + b + c + d

@[reducible] def toySha : Sha where sha256 := fun _ => []

/-- Toy groups: `G1 = G2 = F`, `GT = Unit`; a byte string decodes to its length. -/
@[reducible] def toyGroups : Groups :=
  ⟨F, F, Unit, fun b => some (b.length : F), fun b => some (b.length : F)⟩

attribute [local instance] toyGroups

-- The toy groups' structure: that of `F` and of `Unit`.
@[reducible] def toyG1Group : AddCommGroup G1 := inferInstanceAs (AddCommGroup F)
@[reducible] def toyG2Group : AddCommGroup G2 := inferInstanceAs (AddCommGroup F)
attribute [local instance] toyG1Group toyG2Group
@[reducible] def toyG1Module : Module F G1 := inferInstanceAs (Module F F)
@[reducible] def toyG2Module : Module F G2 := inferInstanceAs (Module F F)
@[reducible] def toyGTGroup : CommGroup GT := inferInstanceAs (CommGroup Unit)
attribute [local instance] toyG1Module toyG2Module toyGTGroup

/-- Toy pairing: always `1` (`GT = Unit` has no other element). -/
@[reducible] def toyPairing : Pairing := ⟨fun _ _ => 1⟩

/-- Toy key: all points `0`. -/
@[reducible] def toyDeployment : Deployment := ⟨⟨0, 0, 0, 0, fun _ => 0⟩⟩


end LeanSpec.NonVacuity
