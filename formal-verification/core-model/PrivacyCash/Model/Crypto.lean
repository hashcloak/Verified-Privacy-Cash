/-
The cryptography the program relies on, left abstract.

The extracted code already takes each primitive as a trait (a Lean record of
functions): Poseidon (`Hasher`), the BN254 scalar field (`PrimeField`),
SHA-256 (`Sha256`) and the curve operations behind Groth16 (`Bn254`). The
model keeps them as parameters (`Crypto`), so every definition and theorem
works for ANY implementation, and whatever a theorem needs from them is
spelled out below as a hypothesis it takes. None of these is an axiom.
-/
import PrivacyCash.Model.Basic
import Mathlib.Data.ZMod.Basic
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Model

/-- The primitives, as the extracted traits. (The traits' methods take no
    `self`, so their `Self` type is irrelevant; `Unit` is used.) -/
structure Crypto where
  /-- Poseidon, `LightHasher<Poseidon>` in the program (`sol_poseidon` on-chain). -/
  hasher : zkcash_core.merkle_tree.Hasher Unit
  /-- The type of BN254 scalar field elements (`ark_bn254::Fr` in the program). -/
  Fr : Type
  /-- Its arithmetic, `ArkFr` in the program. -/
  field : zkcash_core.field.PrimeField Fr
  /-- SHA-256, `SolanaSha256` in the program (`sol_sha256` on-chain). -/
  sha256 : zkcash_core.ext_data.Sha256 Unit
  /-- The `alt_bn128` syscalls and G1 negation, `SolanaBn254` in the program. -/
  bn254 : zkcash_core.groth16.Bn254 Unit

/-- The program's `ProgramVerifier`: the extracted Groth16 verifier
    (`zkcash_core::groth16::verify_proof`) with the program's key, itself
    extracted (`zkcash_core::verifying_key::VERIFYING_KEY`), so the model
    verifies with exactly the bytes the program is compiled with. -/
def Crypto.proofVerifier (c : Crypto) : zkcash_core.transact.ProofVerifier Unit where
  verify p := zkcash_core.groth16.verify_proof c.bn254 p zkcash_core.verifying_key.VERIFYING_KEY

/-! ## Hypotheses a theorem may take about the primitives

Each is a property of the real implementation (checked by tests where noted),
stated only for the inputs an execution actually uses where the property
cannot hold for all inputs. -/

/-- The BN254 scalar field modulus r (`ark_bn254::Fr::MODULUS`). -/
def bn254ScalarModulus : Nat :=
  21888242871839275222246405745257275088548364400416034343698204186575808495617

/-- A 32-byte array read as a big-endian number. -/
def beNat (b : Std.Array U8 32#usize) : Nat := b.val.foldl (fun acc x => acc * 256 + x.val) 0

/-- A 32-byte array read as a little-endian number. -/
def leNat (b : Std.Array U8 32#usize) : Nat := b.val.foldr (fun x acc => acc * 256 + x.val) 0

/-- **Hypothesis (arkworks is correct):** `c.Fr` is the field of integers mod r,
    through `toZMod`, and each `PrimeField` operation computes what its doc
    comment in `zkcash_core::field` says, without panicking. -/
structure FieldCorrect (c : Crypto) where
  toZMod : c.Fr → ZMod bn254ScalarModulus
  injective : Function.Injective toZMod
  from_u64 : ∀ x, ∃ y, c.field.from_u64 x = ok y ∧ toZMod y = (x.val : ZMod bn254ScalarModulus)
  from_be_bytes_mod_order : ∀ b, ∃ y, c.field.from_be_bytes_mod_order b = ok y ∧
    toZMod y = (beNat b : ZMod bn254ScalarModulus)
  from_le_bytes_mod_order : ∀ b, ∃ y, c.field.from_le_bytes_mod_order b = ok y ∧
    toZMod y = (leNat b : ZMod bn254ScalarModulus)
  add : ∀ a b, ∃ y, c.field.add a b = ok y ∧ toZMod y = toZMod a + toZMod b
  sub : ∀ a b, ∃ y, c.field.sub a b = ok y ∧ toZMod y = toZMod a - toZMod b
  neg : ∀ a, ∃ y, c.field.neg a = ok y ∧ toZMod y = - toZMod a
  /-- arkworks orders field elements by their canonical value in `0..r`. -/
  le : ∀ a b, c.field.le a b = ok (decide ((toZMod a).val ≤ (toZMod b).val))
  eq : ∀ a b, ∃ r, c.field.eq a b = ok r ∧ (r = true ↔ a = b)

/-- **Hypothesis (Poseidon collision resistance, per execution):** no two of
    the node pairs in `inputs` hash to the same value. -/
def PoseidonCollisionFree (c : Crypto) (inputs : Set (Pubkey × Pubkey)) : Prop :=
  ∀ x ∈ inputs, ∀ y ∈ inputs, ∀ h,
    c.hasher.hash_pair x.1 x.2 = ok h → c.hasher.hash_pair y.1 y.2 = ok h → x = y

/-- **Hypothesis (Poseidon's zero hashes, checked by a test against
    light_hasher):** entry `i + 1` of `zero_bytes` is the hash of two copies of
    entry `i`, so it is the root of an empty subtree of height `i + 1`. -/
def ZeroBytesConsistent (c : Crypto) : Prop :=
  ∃ z, c.hasher.zero_bytes = ok z ∧
    ∀ i, i + 1 < 41 → c.hasher.hash_pair (z.val[i]!) (z.val[i]!) = ok (z.val[i + 1]!)

/-- **Hypothesis (SHA-256 collision resistance, per execution):** no two of the
    serialized ext data in `inputs` give the same field element after
    `transact`'s `Fr::from_le_bytes_mod_order(sha256(..))`. -/
def ExtDataHashCollisionFree (c : Crypto) (inputs : Set (Slice U8)) : Prop :=
  ∀ x ∈ inputs, ∀ y ∈ inputs, ∀ hx hy fx fy,
    c.sha256.hash x = ok hx → c.sha256.hash y = ok hy →
    c.field.from_le_bytes_mod_order hx = ok fx → c.field.from_le_bytes_mod_order hy = ok fy →
    c.field.eq fx fy = ok true → x = y

/-- A proof's 7 public inputs, in circuit order (as `verify_proof` passes them). -/
def publicInputs (p : zkcash_core.transact.Proof) : List (Std.Array U8 32#usize) :=
  [p.root, p.public_amount, p.ext_data_hash,
   p.input_nullifiers.val[0]!, p.input_nullifiers.val[1]!,
   p.output_commitments.val[0]!, p.output_commitments.val[1]!]

/-- **Hypothesis (Groth16 soundness, per execution):** every proof in `proofs`
    that the program's verifier accepts proves the circuit statement `stmt`
    about its public inputs. `stmt` stands for the relation of
    `circuits/transaction.circom`; the properties of it that theorems use
    (e.g. its two input nullifiers differ) are stated where they are used. -/
def Groth16Sound (c : Crypto) (stmt : List (Std.Array U8 32#usize) → Prop)
    (proofs : Set zkcash_core.transact.Proof) : Prop :=
  ∀ p ∈ proofs, c.proofVerifier.verify p = ok true → stmt (publicInputs p)

/-! ## The field hypothesis can be met

A hypothesis no implementation satisfies would make every theorem assuming it
vacuous. `FieldCorrect` is met by the integers mod r themselves. -/

/-- The integers mod r, with the `PrimeField` operations computed exactly. -/
def zmodField : zkcash_core.field.PrimeField (ZMod bn254ScalarModulus) where
  coremarkerCopyInst := ⟨⟨fun a => ok a, fun _ b => ok b⟩⟩
  from_u64 x := ok (x.val : ZMod bn254ScalarModulus)
  from_be_bytes_mod_order b := ok (beNat b : ZMod bn254ScalarModulus)
  from_le_bytes_mod_order b := ok (leNat b : ZMod bn254ScalarModulus)
  add a b := ok (a + b)
  sub a b := ok (a - b)
  neg a := ok (-a)
  le a b := ok (decide (a.val ≤ b.val))
  eq a b := ok (decide (a = b))

theorem fieldCorrect_satisfiable (c : Crypto) :
    Nonempty (FieldCorrect { c with Fr := ZMod bn254ScalarModulus, field := zmodField }) :=
  ⟨{ toZMod := id
     injective := Function.injective_id
     from_u64 := fun x => ⟨_, rfl, rfl⟩
     from_be_bytes_mod_order := fun b => ⟨_, rfl, rfl⟩
     from_le_bytes_mod_order := fun b => ⟨_, rfl, rfl⟩
     add := fun a b => ⟨_, rfl, rfl⟩
     sub := fun a b => ⟨_, rfl, rfl⟩
     neg := fun a => ⟨_, rfl, rfl⟩
     le := fun a b => rfl
     eq := fun a b => ⟨_, rfl, by simp⟩ }⟩

end PrivacyCash.Model
