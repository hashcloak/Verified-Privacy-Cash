/-
Program-derived addresses (PDAs).

`Pubkey::create_program_address(seeds, program_id)` is
SHA-256(seeds ‖ program_id ‖ "ProgramDerivedAddress"), rejected if on the
ed25519 curve. Solana joins the seeds with no separator, and a bump is just a
last one-byte seed, so the model takes the joined seed bytes, bump included.
`find_program_address(seeds)` picks the canonical bump and returns
`create_program_address(seeds ‖ [bump])`.

The derivation is a hash, so it is NOT injective (there are infinitely many
seed strings and only 2^256 addresses). What we rely on is that nobody finds
two seed strings with the same address. That is never assumed: a theorem that
needs two derived addresses to differ ends in "… or a collision occurs"
(`PdaCollision`), which is a SHA-256 collision, since different seed strings
give different hash inputs.
-/
import PrivacyCash.Model.Basic
open Aeneas Aeneas.Std

namespace PrivacyCash.Model

/-- The bytes of an ASCII seed such as `b"nullifier0"`. -/
def ascii (s : String) : List U8 := s.toList.map (fun c => ⟨BitVec.ofNat 8 c.toNat⟩)

/-- Where the program is deployed, and how Solana derives its addresses. These
    are parameters (not constants), so every definition and theorem holds for
    any deployment (localnet, devnet, mainnet), and a test can run the model
    with the real values. -/
structure Addresses where
  /-- The address the zkcash program is deployed at. -/
  programId : Pubkey
  /-- `Pubkey::create_program_address(seeds, program_id)` for this program, on
      the joined seed bytes (bump included). Any function: it is a hash. Where
      it fails (address on the curve) the real program fails too, so leaving
      that out only lets the model accept more, never less. -/
  createProgramAddress : List U8 → Pubkey
  /-- The bump `find_program_address(seeds, program_id)` picks. -/
  canonicalBump : List U8 → U8

/-- The input `find_program_address(seeds, ..)` hashes: the seeds and the canonical bump. -/
def Addresses.pdaInput (A : Addresses) (seeds : List U8) : List U8 := seeds ++ [A.canonicalBump seeds]

/-- `find_program_address(seeds, program_id).0`: the canonical PDA of `seeds`. -/
def Addresses.pda (A : Addresses) (seeds : List U8) : Pubkey := A.createProgramAddress (A.pdaInput seeds)

/-- **Collision (address derivation):** two different seed strings `s₁` and `s₂`
    (bumps included) derive the same address. -/
def PdaCollision (A : Addresses) (s₁ s₂ : List U8) : Prop :=
  s₁ ≠ s₂ ∧ A.createProgramAddress s₁ = A.createProgramAddress s₂

/-! ## The PDAs of Privacy Cash (seeds from `#[derive(Accounts)]` in lib.rs) -/

/-- `seeds = [b"merkle_tree"]`: the SOL Merkle tree. -/
def merkleTreeSeeds : List U8 := ascii "merkle_tree"
/-- `seeds = [b"merkle_tree", mint.key().as_ref()]`: an SPL token's tree. -/
def splMerkleTreeSeeds (mint : Pubkey) : List U8 := ascii "merkle_tree" ++ mint.val
/-- `seeds = [b"tree_token"]`: the SOL pool. -/
def treeTokenSeeds : List U8 := ascii "tree_token"
/-- `seeds = [b"global_config"]`. -/
def globalConfigSeeds : List U8 := ascii "global_config"
/-- `seeds = [b"nullifier0", n.as_ref()]`: nullifier `n` spent in slot 0. -/
def nullifier0Seeds (n : Pubkey) : List U8 := ascii "nullifier0" ++ n.val
/-- `seeds = [b"nullifier1", n.as_ref()]`: nullifier `n` spent in slot 1. -/
def nullifier1Seeds (n : Pubkey) : List U8 := ascii "nullifier1" ++ n.val

/-! ## Distinct seed strings (no assumptions) -/

/-- Two byte strings `pre ++ x` with same-length prefixes are equal only if
    the prefixes and the suffixes are. -/
theorem append_eq_iff {pre₁ pre₂ x₁ x₂ : List U8} (h : pre₁.length = pre₂.length) :
    pre₁ ++ x₁ = pre₂ ++ x₂ ↔ pre₁ = pre₂ ∧ x₁ = x₂ :=
  ⟨fun e => List.append_inj e h, fun ⟨a, b⟩ => by rw [a, b]⟩

/-- Same-slot nullifier seeds (with any bumps) match only for the same nullifier. -/
theorem nullifier0Seeds_inj {n m : Pubkey} {b c : U8}
    (h : nullifier0Seeds n ++ [b] = nullifier0Seeds m ++ [c]) : n = m := by
  rw [nullifier0Seeds, nullifier0Seeds, List.append_assoc, List.append_assoc,
    append_eq_iff rfl, append_eq_iff (by simp)] at h
  exact (Std.Array.eq_iff n m).mpr h.2.1

theorem nullifier1Seeds_inj {n m : Pubkey} {b c : U8}
    (h : nullifier1Seeds n ++ [b] = nullifier1Seeds m ++ [c]) : n = m := by
  rw [nullifier1Seeds, nullifier1Seeds, List.append_assoc, List.append_assoc,
    append_eq_iff rfl, append_eq_iff (by simp)] at h
  exact (Std.Array.eq_iff n m).mpr h.2.1

/-- "nullifier0" and "nullifier1" differ in their last byte. -/
theorem nullifier0Seeds_ne_nullifier1Seeds (n m : Pubkey) (b c : U8) :
    nullifier0Seeds n ++ [b] ≠ nullifier1Seeds m ++ [c] := by
  intro h
  rw [nullifier0Seeds, nullifier1Seeds, List.append_assoc, List.append_assoc,
    append_eq_iff (by decide)] at h
  exact absurd h.1 (by decide)

/-- Every Privacy Cash seed pattern has its own length, except the two
    nullifier slots (42 bytes each, told apart above). -/
theorem seed_lengths (mint n : Pubkey) :
    merkleTreeSeeds.length = 11 ∧ (splMerkleTreeSeeds mint).length = 43 ∧
    treeTokenSeeds.length = 10 ∧ globalConfigSeeds.length = 13 ∧
    (nullifier0Seeds n).length = 42 ∧ (nullifier1Seeds n).length = 42 := by
  simp [merkleTreeSeeds, splMerkleTreeSeeds, treeTokenSeeds, globalConfigSeeds,
    nullifier0Seeds, nullifier1Seeds, ascii]

/-! ## Distinct addresses, or a collision on the inputs involved -/

variable {A : Addresses}

/-- Different seed strings derive different addresses, or they collide. -/
theorem createProgramAddress_ne_or {s₁ s₂ : List U8} (hne : s₁ ≠ s₂) :
    A.createProgramAddress s₁ ≠ A.createProgramAddress s₂ ∨ PdaCollision A s₁ s₂ := by
  by_cases h : A.createProgramAddress s₁ = A.createProgramAddress s₂
  · exact Or.inr ⟨hne, h⟩
  · exact Or.inl h

/-- Nullifier accounts of the same slot are equal only for the same nullifier, or their seeds
    collide. -/
theorem nullifier0_pda_inj {n m : Pubkey}
    (h : A.pda (nullifier0Seeds n) = A.pda (nullifier0Seeds m)) :
    n = m ∨ PdaCollision A (A.pdaInput (nullifier0Seeds n)) (A.pdaInput (nullifier0Seeds m)) := by
  by_cases hs : A.pdaInput (nullifier0Seeds n) = A.pdaInput (nullifier0Seeds m)
  · exact Or.inl (nullifier0Seeds_inj hs)
  · exact Or.inr ⟨hs, h⟩

theorem nullifier1_pda_inj {n m : Pubkey}
    (h : A.pda (nullifier1Seeds n) = A.pda (nullifier1Seeds m)) :
    n = m ∨ PdaCollision A (A.pdaInput (nullifier1Seeds n)) (A.pdaInput (nullifier1Seeds m)) := by
  by_cases hs : A.pdaInput (nullifier1Seeds n) = A.pdaInput (nullifier1Seeds m)
  · exact Or.inl (nullifier1Seeds_inj hs)
  · exact Or.inr ⟨hs, h⟩

/-- A slot-0 nullifier account is never a slot-1 one, or their seeds collide. -/
theorem nullifier0_ne_nullifier1 (n m : Pubkey) :
    A.pda (nullifier0Seeds n) ≠ A.pda (nullifier1Seeds m) ∨
      PdaCollision A (A.pdaInput (nullifier0Seeds n)) (A.pdaInput (nullifier1Seeds m)) :=
  createProgramAddress_ne_or (nullifier0Seeds_ne_nullifier1Seeds n m _ _)

/-- Inputs of different lengths are different inputs. -/
theorem ne_of_length_ne {s₁ s₂ : List U8} (h : s₁.length ≠ s₂.length) : s₁ ≠ s₂ :=
  fun e => h (congrArg List.length e)

/-- The SOL tree, pool and config (with any bumps) are three different accounts, or two of their
    seeds collide. -/
theorem singleton_pdas_distinct (b₁ b₂ b₃ : U8) :
    (A.createProgramAddress (merkleTreeSeeds ++ [b₁]) ≠
        A.createProgramAddress (treeTokenSeeds ++ [b₂]) ∨
      PdaCollision A (merkleTreeSeeds ++ [b₁]) (treeTokenSeeds ++ [b₂])) ∧
    (A.createProgramAddress (merkleTreeSeeds ++ [b₁]) ≠
        A.createProgramAddress (globalConfigSeeds ++ [b₃]) ∨
      PdaCollision A (merkleTreeSeeds ++ [b₁]) (globalConfigSeeds ++ [b₃])) ∧
    (A.createProgramAddress (treeTokenSeeds ++ [b₂]) ≠
        A.createProgramAddress (globalConfigSeeds ++ [b₃]) ∨
      PdaCollision A (treeTokenSeeds ++ [b₂]) (globalConfigSeeds ++ [b₃])) := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := seed_lengths default default
  refine ⟨createProgramAddress_ne_or (ne_of_length_ne ?_),
    createProgramAddress_ne_or (ne_of_length_ne ?_),
    createProgramAddress_ne_or (ne_of_length_ne ?_)⟩ <;> simp [h1, h3, h4]

/-- A nullifier account (any bump) is never the SOL tree, pool or config (any bumps), or their
    seeds collide. -/
theorem nullifier_ne_singletons (n : Pubkey) (b : U8) (s : List U8)
    (hs : s ∈ [merkleTreeSeeds, treeTokenSeeds, globalConfigSeeds]) (c : U8) :
    (A.createProgramAddress (nullifier0Seeds n ++ [b]) ≠ A.createProgramAddress (s ++ [c]) ∨
      PdaCollision A (nullifier0Seeds n ++ [b]) (s ++ [c])) ∧
    (A.createProgramAddress (nullifier1Seeds n ++ [b]) ≠ A.createProgramAddress (s ++ [c]) ∨
      PdaCollision A (nullifier1Seeds n ++ [b]) (s ++ [c])) := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := seed_lengths default n
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  refine ⟨createProgramAddress_ne_or (ne_of_length_ne ?_),
    createProgramAddress_ne_or (ne_of_length_ne ?_)⟩ <;>
  rcases hs with rfl | rfl | rfl <;> simp [h1, h3, h4, h5, h6]

end PrivacyCash.Model
