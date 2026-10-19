/-
Checks the account sizes the model uses for rent (`treeAccountSpace`, ...,
in PrivacyCash/Model/Program.lean) against the program's real
`8 + size_of::<T>()`. The values between the GENERATED markers are printed by
the fork's `programs/zkcash/tests/model_vectors/mod.rs` (`print_account_spaces`);
`scripts/check_vectors.sh` regenerates them and fails if they differ.
-/
import PrivacyCash
open PrivacyCash.Model

namespace PrivacyCash.Tests.AccountSpaces

-- BEGIN GENERATED
/-- (account type, `8 + size_of::<T>()`) -/
def accountSpaces : List (String × Nat) := [
  ("MerkleTreeAccount", 4136),
  ("TreeTokenAccount", 41),
  ("GlobalConfig", 48),
  ("NullifierAccount", 9)
]
-- END GENERATED

/-- The model's size for each account type. -/
def modelSpaces : List (String × Nat) :=
  [("MerkleTreeAccount", treeAccountSpace), ("TreeTokenAccount", treeTokenAccountSpace),
   ("GlobalConfig", globalConfigSpace), ("NullifierAccount", nullifierAccountSpace)]

#guard modelSpaces = accountSpaces

end PrivacyCash.Tests.AccountSpaces
