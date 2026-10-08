/-
Proofs about `zkcash_core::merkle_tree` (the extracted code is in
PrivacyCash/Extracted/Funs.lean, generated from crates/zkcash_core).
-/
import PrivacyCash.Extracted.Funs
open Aeneas Aeneas.Std Result

namespace zkcash_core.merkle_tree

/-- Comparing the all-zero root with itself returns `true`.
    (Rust: `root == [0u8; 32]` when `root` is `[0u8; 32]`.) -/
theorem zero_root_eq_self :
    core.array.equality.PartialEqArray.eq core.cmp.PartialEqU8
      (Array.repeat 32#usize 0#u8) (Array.repeat 32#usize 0#u8) = ok true := by
  simp [core.array.equality.PartialEqArray.eq]
  rfl

/-- The all-zero root is never accepted, whatever the tree contains, and
    checking it never panics.
    (Rust: `if root == [0u8; 32] { return false; }`) -/
theorem is_known_root_zero (tree_account : MerkleTreeAccount) :
    is_known_root tree_account (Array.repeat 32#usize 0#u8) = ok false := by
  unfold is_known_root
  simp [zero_root_eq_self]

end zkcash_core.merkle_tree
