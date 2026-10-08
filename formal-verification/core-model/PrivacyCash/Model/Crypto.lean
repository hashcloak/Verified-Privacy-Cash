/-
The cryptography the program relies on, left abstract.

The extracted code already takes each primitive as a trait (a Lean record of
functions): Poseidon (`Hasher`), the BN254 scalar field (`PrimeField`),
SHA-256 (`Sha256`) and the curve operations behind Groth16 (`Bn254`). The
model keeps the ones it cannot define as parameters (`Crypto`), so every
definition and theorem works for ANY implementation, and whatever a theorem
needs from them is spelled out as a hypothesis it takes. None of these is an
axiom. What is arkworks code inside the program is defined instead: the
scalar field (`Field.lean`) and G1 negation (`Bn254.lean`). What stays a
parameter is executed by the validator: Poseidon, SHA-256 and the
`alt_bn128` syscalls.
-/
import PrivacyCash.Model.Basic
import PrivacyCash.Model.Bn254
import PrivacyCash.Model.Field
import Mathlib.Data.ZMod.Basic
open Aeneas Aeneas.Std Result

namespace PrivacyCash.Model

/-- The primitives, as the extracted traits. (The traits' methods take no
    `self`, so their `Self` type is irrelevant; `Unit` is used.) -/
structure Crypto where
  /-- Poseidon, `LightHasher<Poseidon>` in the program (`sol_poseidon` on-chain). -/
  hasher : zkcash_core.merkle_tree.Hasher Unit
  /-- SHA-256, `SolanaSha256` in the program (`sol_sha256` on-chain). -/
  sha256 : zkcash_core.ext_data.Sha256 Unit
  /-- The `alt_bn128` syscalls `SolanaBn254` calls (executed by the validator). -/
  altBn128 : AltBn128

/-- The program's `SolanaBn254`: the syscalls, plus G1 negation as defined in
    `Bn254.lean`. -/
def Crypto.bn254 (c : Crypto) : zkcash_core.groth16.Bn254 Unit := solanaBn254 c.altBn128

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
    `transact`'s `Fr::from_le_bytes_mod_order(sha256(..))`, i.e. the digest
    read little-endian and reduced mod r. -/
def ExtDataHashCollisionFree (c : Crypto) (inputs : Set (Slice U8)) : Prop :=
  ∀ x ∈ inputs, ∀ y ∈ inputs, ∀ hx hy,
    c.sha256.hash x = ok hx → c.sha256.hash y = ok hy →
    (leNat hx : Fr) = (leNat hy : Fr) → x = y

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

end PrivacyCash.Model
