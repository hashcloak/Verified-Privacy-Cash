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
two seed strings with the same address. That is never an axiom here: theorems
take `PdaCollisionFree S` as a hypothesis for the finitely many seed strings
`S` they are about, which is true of SHA-256 on any real execution.
-/
import PrivacyCash.Model.Basic
open Aeneas Aeneas.Std

namespace PrivacyCash.Model

/-- The bytes of an ASCII seed such as `b"nullifier0"`. -/
def ascii (s : String) : List U8 := s.toList.map (fun c => ⟨BitVec.ofNat 8 c.toNat⟩)

/-- `Pubkey::create_program_address(seeds, program_id)` for this program, on the
    joined seed bytes (bump included). Left abstract (it is a hash). Where it
    fails (address on the curve) the real program fails too, so leaving that
    out only lets the model accept more, never less. -/
opaque createProgramAddress (seedBytes : List U8) : Pubkey

/-- The bump `find_program_address(seeds, program_id)` picks. Left abstract. -/
opaque canonicalBump (seeds : List U8) : U8

/-- The input `find_program_address(seeds, ..)` hashes: the seeds and the canonical bump. -/
def pdaInput (seeds : List U8) : List U8 := seeds ++ [canonicalBump seeds]

/-- `find_program_address(seeds, program_id).0`: the canonical PDA of `seeds`. -/
def pda (seeds : List U8) : Pubkey := createProgramAddress (pdaInput seeds)

/-- **Hypothesis (SHA-256 collision resistance, per execution):** no two of the
    seed strings in `inputs` (bumps included) derive the same address. -/
def PdaCollisionFree (inputs : Set (List U8)) : Prop :=
  ∀ s₁ ∈ inputs, ∀ s₂ ∈ inputs, createProgramAddress s₁ = createProgramAddress s₂ → s₁ = s₂

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

/-! ## Distinct addresses, given collision-freedom of the inputs involved -/

/-- Different inputs in a collision-free set derive different addresses. -/
theorem createProgramAddress_ne {S : Set (List U8)} (hcf : PdaCollisionFree S)
    {s₁ s₂ : List U8} (h₁ : s₁ ∈ S) (h₂ : s₂ ∈ S) (hne : s₁ ≠ s₂) :
    createProgramAddress s₁ ≠ createProgramAddress s₂ :=
  fun e => hne (hcf s₁ h₁ s₂ h₂ e)

/-- Nullifier accounts of the same slot are equal only for the same nullifier. -/
theorem nullifier0_pda_inj {n m : Pubkey}
    (hcf : PdaCollisionFree {pdaInput (nullifier0Seeds n), pdaInput (nullifier0Seeds m)})
    (h : pda (nullifier0Seeds n) = pda (nullifier0Seeds m)) : n = m :=
  nullifier0Seeds_inj (hcf _ (by simp) _ (by simp) h :)

theorem nullifier1_pda_inj {n m : Pubkey}
    (hcf : PdaCollisionFree {pdaInput (nullifier1Seeds n), pdaInput (nullifier1Seeds m)})
    (h : pda (nullifier1Seeds n) = pda (nullifier1Seeds m)) : n = m :=
  nullifier1Seeds_inj (hcf _ (by simp) _ (by simp) h :)

/-- A slot-0 nullifier account is never a slot-1 one. -/
theorem nullifier0_ne_nullifier1 {n m : Pubkey}
    (hcf : PdaCollisionFree {pdaInput (nullifier0Seeds n), pdaInput (nullifier1Seeds m)}) :
    pda (nullifier0Seeds n) ≠ pda (nullifier1Seeds m) :=
  createProgramAddress_ne hcf (by simp) (by simp) (nullifier0Seeds_ne_nullifier1Seeds n m _ _)

/-- Inputs of different lengths are different inputs. -/
theorem ne_of_length_ne {s₁ s₂ : List U8} (h : s₁.length ≠ s₂.length) : s₁ ≠ s₂ :=
  fun e => h (congrArg List.length e)

/-- The SOL tree, pool and config (with any bumps) are three different accounts. -/
theorem singleton_pdas_distinct (b₁ b₂ b₃ : U8)
    (hcf : PdaCollisionFree
      {merkleTreeSeeds ++ [b₁], treeTokenSeeds ++ [b₂], globalConfigSeeds ++ [b₃]}) :
    createProgramAddress (merkleTreeSeeds ++ [b₁]) ≠ createProgramAddress (treeTokenSeeds ++ [b₂]) ∧
    createProgramAddress (merkleTreeSeeds ++ [b₁]) ≠ createProgramAddress (globalConfigSeeds ++ [b₃]) ∧
    createProgramAddress (treeTokenSeeds ++ [b₂]) ≠ createProgramAddress (globalConfigSeeds ++ [b₃]) := by
  obtain ⟨h1, -, h3, h4, -, -⟩ := seed_lengths default default
  refine ⟨createProgramAddress_ne hcf (by simp) (by simp) (ne_of_length_ne ?_),
    createProgramAddress_ne hcf (by simp) (by simp) (ne_of_length_ne ?_),
    createProgramAddress_ne hcf (by simp) (by simp) (ne_of_length_ne ?_)⟩ <;> simp [h1, h3, h4]

/-- A nullifier account (any bump) is never the SOL tree, pool or config (any bumps). -/
theorem nullifier_ne_singletons (n : Pubkey) (b : U8) (s : List U8)
    (hs : s ∈ [merkleTreeSeeds, treeTokenSeeds, globalConfigSeeds]) (c : U8)
    (hcf : PdaCollisionFree {nullifier0Seeds n ++ [b], nullifier1Seeds n ++ [b], s ++ [c]}) :
    createProgramAddress (nullifier0Seeds n ++ [b]) ≠ createProgramAddress (s ++ [c]) ∧
    createProgramAddress (nullifier1Seeds n ++ [b]) ≠ createProgramAddress (s ++ [c]) := by
  obtain ⟨h1, -, h3, h4, h5, h6⟩ := seed_lengths default n
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  refine ⟨createProgramAddress_ne hcf (by simp) (by simp) (ne_of_length_ne ?_),
    createProgramAddress_ne hcf (by simp) (by simp) (ne_of_length_ne ?_)⟩ <;>
  rcases hs with rfl | rfl | rfl <;> simp [h1, h3, h4, h5, h6]

end PrivacyCash.Model
