import Connection.Mapping
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # Assumptions about the code model

REVIEW SURFACE. Assumptions the connection theorems need about the code side alone: the
deployment, the Solana runtime and Anchor, and the cryptographic primitives as the code uses
them. They say nothing about the spec. Core-model does not state them; its own assumptions are
listed in `core-model/README.md`.

What links the code to the spec, and what the spec deliberately leaves out, is in
`Hypotheses.lean`.

1. `DeploymentFacts`: the program is not the System Program.
2. `SolanaFacts` (per transaction): no program-derived address signs. Positive rent is part of
   core-model's `Run` (`TxEnv.RentPositive`).
3. `CryptoFacts` (per transaction): the circuit makes the two nullifiers differ; SHA-256 makes the
   two new nullifier accounts' addresses differ.
4. `PairingLaws`, with core-model's syscall contracts `AltBn128Contracts`: the verifier bridge.
5. `ExecutionAssumptions` (`run_connection`): the fixed addresses differ, and every `transact`
   satisfies `SolanaFacts` and `CryptoFacts`.
6. For completeness only: `HashesSucceed`, `SyscallsSucceed`, `KeyG2Decodes`: the primitives
   answer at all (bundled with `HashesAgree` in `CompletenessAssumptions`, `Hypotheses.lean`).
7. For G3a and G3b for the code only: `ProgramAccountsInPlace`, `NullifierAddressesFree`:
   Anchor's account constraints hold (not machine-checked).
-/

namespace Connection

/-- `DeploymentFacts d` (assumed): facts about where the program is deployed. -/
structure DeploymentFacts (d : Deployment) : Prop where
  /-- The program is not the System Program. The code model needs this because it checks
      whether an account is still free by asking whether the System Program owns it: for the
      nullifier accounts (so no nullifier is spent twice) and for the tree, pool and config (so
      `initialize` runs once). True of every deployment: no program can be deployed at the
      System Program's address. -/
  programNotSystem : d.programId ≠ systemProgram

/-- `SolanaFacts d tx` (assumed, about the Solana runtime, for this transaction): no
    program-derived address signs. (That the rent is positive is part of core-model's `Run`.) -/
structure SolanaFacts (d : Deployment) (tx : TxEnv) : Prop where
  /-- No program-derived address signs the transaction: a PDA is off the ed25519 curve, so it
      has no private key. So the signer is neither the pool nor a new nullifier account. -/
  pdasDoNotSign : ∀ seeds, d.pda seeds ∉ tx.signers

/-- `CryptoFacts d proof` (assumed, about the circuit and SHA-256, for this transaction):
    the two input nullifiers differ, and so do the addresses of the two new nullifier
    accounts. -/
structure CryptoFacts (d : Deployment) (proof : zkcash_core.transact.Proof) : Prop where
  distinctNullifiers : proof.input_nullifiers.val[0]! ≠ proof.input_nullifiers.val[1]!
  /-- The two new nullifier accounts (slot 0 of nullifier 0, slot 1 of nullifier 1) have
      different addresses (SHA-256 collision resistance of the PDA derivation). -/
  nullifierAddressesDiffer : PdaCollisionFree d.toAddresses
    {d.pdaInput (nullifier0Seeds proof.input_nullifiers.val[0]!),
     d.pdaInput (nullifier1Seeds proof.input_nullifiers.val[1]!)}

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT]

/-- `PairingLaws e` (assumed, about the `alt_bn128` pairing, for the verifier bridge): pairing
    with `-a` gives the inverse. True of the BN254 optimal ate pairing. Needed because the code
    checks the Groth16 equation as a product with `-A` (`e(-A, B) · e(α, β) · e(vkX, γ) · e(C, δ) = 1`),
    while the spec states it as `e(A, B) = e(α, β) · e(vkX, γ) · e(C, δ)`. -/
structure PairingLaws (e : G1 → G2 → GT) : Prop where
  neg_left : ∀ (a : G1) (b : G2), e (-a) b = (e a b)⁻¹

end

/-- `StepAssumptions d rent tx ix`: the assumptions one step of an execution needs: a
    `transact` satisfies the per-transaction assumptions (`SolanaFacts`, `CryptoFacts`). -/
def StepAssumptions (d : Deployment) (rent : Nat → U64) (tx : TxEnv) : Instruction → Prop
  | .transact _ proof _ _ _ _ => SolanaFacts d tx ∧ CryptoFacts d proof
  | _ => True

/-- `ExecutionAssumptions d rent sGenesis evs` (assumed, used by `run_connection`): for the
    execution from `sGenesis` with events `evs`, the program's three fixed accounts are different,
    and every `transact` satisfies `SolanaFacts` and `CryptoFacts` (`StepAssumptions`). -/
structure ExecutionAssumptions (d : Deployment) (rent : Nat → U64) (sGenesis : State) (evs : List Event) :
    Prop where
  /-- The program's three fixed accounts (the tree, the pool, the config) have different
      addresses (SHA-256 collision resistance of the PDA derivation, as in
      `CryptoFacts.nullifierAddressesDiffer`). Without it, `initialize` could write two of
      them to the same account. -/
  fixedAddressesDiffer : PdaCollisionFree d.toAddresses
    {d.pdaInput merkleTreeSeeds, d.pdaInput treeTokenSeeds, d.pdaInput globalConfigSeeds}
  /-- Every program step of the execution, from the state the execution reached before it,
      satisfies `StepAssumptions`. -/
  eachStep : ∀ pre post s tx ix em, evs = pre ++ .program tx ix em :: post → Run d sGenesis pre s →
    StepAssumptions d rent tx ix

/-! ## For handler completeness only

Safety ("code accepts ⟹ spec allows") needs only what a returned answer means. Completeness
("spec allows ⟹ code accepts") also needs the primitives to answer at all. -/

/-- `HashesSucceed c` (assumed, handler completeness only): the hash functions return a
    value where the program needs one. True of the real libraries: `light-poseidon` fails only on inputs ≥ p,
    and the program's Poseidon inputs are canonical (stored subtrees, zero hashes, the
    commitments the verifier range-checked, and Poseidon's own outputs); SHA-256 always
    returns. Separate from `HashesAgree`, which says only what a returned value is. -/
structure HashesSucceed (c : Crypto) : Prop where
  /-- Poseidon returns a value on canonical inputs. -/
  poseidon : ∀ a b, Canonical a → Canonical b → ∃ h, c.hasher.hash_pair a b = ok h
  /-- SHA-256 always returns a value. -/
  sha256 : ∀ x, ∃ h, c.sha256.hash x = ok h

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT] {s : AltBn128}

/-- `SyscallsSucceed C` (assumed, handler completeness only): the `alt_bn128` syscalls return
    a value on valid points, and the pairing answers 1 exactly when the product of the pairings is 1. The
    converse of core-model's `AltBn128Contracts`, which only say what a returned answer means.
    True of Solana's syscalls, which fail only on invalid input. To be raised with the
    core-model team (`TODO.md`): if they add it to the contracts, this bundle can go. -/
structure SyscallsSucceed (C : AltBn128Contracts s G1 G2 GT) : Prop where
  /-- Multiplication returns a value when its point (bytes 0..63) decodes. -/
  mul : ∀ input, C.decodeG1 (bytesAt input 0 64#usize (by simp)) ≠ none →
    ∃ out, s.multiplication input = some out
  /-- Addition returns a value when both points decode. -/
  add : ∀ input, C.decodeG1 (bytesAt input 0 64#usize (by simp)) ≠ none →
    C.decodeG1 (bytesAt input 64 64#usize (by simp)) ≠ none → ∃ out, s.addition input = some out
  /-- The pairing returns a value when its eight points decode, and that value ends in 1
      exactly when the product of the four pairings is 1. -/
  pairing : ∀ input (P₁ P₂ P₃ P₄ : G1) (Q₁ Q₂ Q₃ Q₄ : G2),
    C.decodeG1 (bytesAt input 0 64#usize (by simp)) = some P₁ →
    C.decodeG2 (bytesAt input 64 128#usize (by simp)) = some Q₁ →
    C.decodeG1 (bytesAt input 192 64#usize (by simp)) = some P₂ →
    C.decodeG2 (bytesAt input 256 128#usize (by simp)) = some Q₂ →
    C.decodeG1 (bytesAt input 384 64#usize (by simp)) = some P₃ →
    C.decodeG2 (bytesAt input 448 128#usize (by simp)) = some Q₃ →
    C.decodeG1 (bytesAt input 576 64#usize (by simp)) = some P₄ →
    C.decodeG2 (bytesAt input 640 128#usize (by simp)) = some Q₄ →
    ∃ out, s.pairing input = some out ∧
      (out.val[31]! = 1#u8 ↔ C.e P₁ Q₁ * C.e P₂ Q₂ * C.e P₃ Q₃ * C.e P₄ Q₄ = 1)

/-- `KeyG2Decodes C` (assumed, handler completeness only): the syscalls decode the three G2
    points of the program's verifying key. True: the trusted setup produced valid points, and the real
    program verifies real proofs on chain. Needed because `programKey` reads an undecodable
    key point as `0`, so without it the spec could accept a proof the code rejects. The
    key's G1 points are checked by computation (`key_alpha_decodes`, `key_ic_decodes`); the
    G2 decoding is a parameter of core-model's contracts, so it cannot be checked in Lean. -/
structure KeyG2Decodes (C : AltBn128Contracts s G1 G2 GT) : Prop where
  beta : C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_beta_g2 ≠ none
  gamma : C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_gamme_g2 ≠ none
  delta : C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_delta_g2 ≠ none

end

/-! ## For G3a and G3b for the code: Anchor's account constraints hold -/

/-- `ProgramAccountsInPlace d s tree tt config` (assumed; could be proved as an invariant): the
    program's three accounts hold `tree`, `tt` and `config` at their canonical addresses, which
    their stored bumps derive. `initialize` sets those bumps and no instruction changes them. -/
structure ProgramAccountsInPlace (d : Deployment) (s : State)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (tt : zkcash_core.admin.TreeTokenAccount)
    (config : zkcash_core.admin.GlobalConfig) : Prop where
  tree : HoldsTree d.programId s (treeAddr d) tree ∧
    treeAddr d = d.toAddresses.createProgramAddress (merkleTreeSeeds ++ [tree.bump])
  pool : HoldsTreeToken d.programId s (poolAddr d) tt ∧
    poolAddr d = d.toAddresses.createProgramAddress (treeTokenSeeds ++ [tt.bump])
  config : HoldsGlobalConfig d.programId s (configAddr d) config ∧
    configAddr d = d.toAddresses.createProgramAddress (globalConfigSeeds ++ [config.bump])

/-- `NullifierAddressesFree d s proof` (assumed, not machine-checked): Anchor's constraints on the
    four nullifier addresses hold: `init` for the two new accounts, `SystemAccount` for the other
    two.

    Why it holds for an unspent nullifier:
    - SOLANA FACT: only this program can create an account at its derived addresses, since it alone
      can sign for them; anyone else can only send lamports there, which `init` handles;
    - the program creates nullifier accounts only in `transact`, for the two nullifiers it spends.

    `Spec`'s `newNullifiers` says the nullifiers are unspent; proving this from it is future work
    (`TODO.md`). Until then, G3 for the code doesn't check this logic in the program. -/
structure NullifierAddressesFree (d : Deployment) (s : State)
    (proof : zkcash_core.transact.Proof) : Prop where
  new0 : Initializable s (d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!))
  new1 : Initializable s (d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!))
  other0 : IsSystemAccount s (d.pda (nullifier0Seeds proof.input_nullifiers.val[1]!))
  other1 : IsSystemAccount s (d.pda (nullifier1Seeds proof.input_nullifiers.val[0]!))

end Connection
