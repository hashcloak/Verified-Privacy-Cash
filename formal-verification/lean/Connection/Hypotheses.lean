import Connection.Mapping
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # The hypotheses of the connection theorem for `transact`

REVIEW SURFACE. Besides "the code model accepted the transaction", the connection theorems
(`Connection/ConnectionTheorems.lean`) take these hypotheses. They are of different kinds, and should
be read differently:

1. `HashesAgree` (ASSUMED, about the deployment's hash functions): the code's Poseidon, zero
   hashes and SHA-256 compute the spec's `H2`, `Z` and `sha256`; Poseidon's outputs and the
   zero hashes are canonical bytes (below the field modulus).
2. `WellFormed` (INVARIANT, PROVED): facts about the program's own accounts. Proved for every
   state an execution reaches from genesis, so no theorem in `ConnectionTheorems.lean` takes it as a
   hypothesis.
3. `SolanaFacts` (ASSUMED, about the Solana runtime): the rent is positive, the transaction's
   data fits in memory, and the pool's address does not sign.
4. `CryptoFacts` (ASSUMED, about the circuit and SHA-256, for this transaction): the circuit
   makes the two nullifiers differ; SHA-256 makes the two new nullifier accounts' addresses
   differ.
5. `PairingLaws` (ASSUMED, about the `alt_bn128` pairing), with core-model's syscall contracts
   `AltBn128Contracts`: needed by the verifier bridge.
6. `OutsideSpecDetail` (BY DESIGN): Solana details the spec deliberately does not model, as it
   is written at the level of the documentation. Each field rules one out; `transact_connection`
   does not cover transactions where such a detail matters. Not a defect of the code or the
   spec. `run_connection` does not take it: there these details are changes the spec allows
   between transactions.

7. For handler completeness only: `HashesSucceed`, `SyscallsSucceed` (ASSUMED: the primitives
   answer at all), and `KeyG2Decodes` (approved assumption).

No code/spec difference is currently excluded: no theorem has a `Findings` hypothesis.

Not a hypothesis here, but relied on: core-model's `EnvStep` (outside actions cannot change the
owner or data of an account the program owns, and the program never closes one). The
double-spend protection rests on it: a nullifier account, once created, stays. Check it in
core-model (`PrivacyCash/Model/Execution.lean`).
-/

namespace Connection

variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-- **Assumed**: the code's hash functions compute the spec's. Each is stated as "if the code's
    hash returns `h`, then `h` is the spec's hash", so nothing is claimed about inputs it rejects. -/
structure HashesAgree (c : Crypto) : Prop where
  /-- Poseidon of two tree nodes is the spec's `H2`. -/
  poseidon : ∀ a b h, c.hasher.hash_pair a b = ok h → toF h = LeanSpec.PoseidonHashes.H2 (toF a) (toF b)
  /-- The program's zero hashes are the spec's empty-subtree roots `Z 0, …, Z 26`. -/
  zeroBytes : ∃ z, c.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = LeanSpec.Z i
  /-- SHA-256 is the spec's `sha256` (used for the external data hash). -/
  sha256 : ∀ x h, c.sha256.hash x = ok h → toBytes h.val = LeanSpec.Sha.sha256 (toBytes x.val)
  /-- Poseidon's outputs are canonical: their big-endian value is below the field modulus.
      True of the program's hasher: `light-poseidon` computes in `ark_bn254::Fr` and writes
      the result with `into_bigint().to_bytes_be()`, which is always below the field's modulus,
      and that modulus is the spec's `p` (`p_eq`, `Connection/Mapping.lean`). -/
  poseidonCanonical : ∀ a b h, c.hasher.hash_pair a b = ok h → Canonical h
  /-- The program's zero hashes `0, …, 26` are canonical. True: they are Poseidon outputs
      (checked by the fork's `zero_bytes_are_empty_subtree_roots` test), and entry 0 is zero. -/
  zeroBytesCanonical : ∃ z, c.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → Canonical (z.val[i]!)

/-- **Invariant, proved**: facts about the program's own accounts. They hold in every state an
    execution reaches from genesis, with `spent` the nullifiers that execution spent (proved in
    `Proofs/WellFormed.lean`), so no theorem in `ConnectionTheorems.lean` assumes it. -/
structure WellFormed (d : Deployment) (spent : Finset LeanSpec.F) (s : State) : Prop where
  /-- The program is not the system program (so "owned by the program" and "not yet created"
      are different things). -/
  programNotSystem : d.programId ≠ systemProgram
  /-- Every Merkle tree the program owns is the SOL tree at its canonical address, with height
      26, a history of 100 roots and a current root index below 100. -/
  tree : ∀ k t, HoldsTree d.programId s k t → k = treeAddr d ∧ TreeShape t
  /-- Every pool account the program owns is the SOL pool at its canonical address. -/
  pool : ∀ k p, HoldsTreeToken d.programId s k p → k = poolAddr d
  /-- Every config the program owns is at its canonical address, and its deposit fee rate,
      withdrawal fee rate and fee error margin are each at most 10000 basis points (100%);
      `update_global_config` refuses larger values. -/
  config : ∀ k c, HoldsGlobalConfig d.programId s k c → k = configAddr d ∧
    c.deposit_fee_rate.val ≤ 10000 ∧ c.withdrawal_fee_rate.val ≤ 10000 ∧
    c.fee_error_margin.val ≤ 10000
  /-- Every nullifier the connection tracks as spent is the field value of some canonical
      32-byte nullifier whose nullifier account (slot 0 or slot 1) is owned by the program. -/
  spentRecorded : ∀ x ∈ spent, ∃ n : Pubkey, Canonical n ∧ toF n = x ∧
    ((s (d.pda (nullifier0Seeds n))).owner = d.programId ∨
      (s (d.pda (nullifier1Seeds n))).owner = d.programId)
  /-- Every root stored in the history of a tree the program owns is canonical (big-endian
      value below the field modulus): the program stores only the zero hashes, zero bytes and
      Poseidon outputs there (`HashesAgree.zeroBytesCanonical`, `poseidonCanonical`). -/
  storedRoots : ∀ k t, HoldsTree d.programId s k t → ∀ j : Fin 100, Canonical t.root_history.val[j.val]!
  /-- Every subtree stored in a tree the program owns is canonical: the program stores only
      zero hashes, leaves the verifier range-checked, and Poseidon outputs there. Needed by
      handler completeness (Poseidon answers only on canonical inputs). -/
  storedSubtrees : ∀ k t, HoldsTree d.programId s k t → ∀ j : Fin 26, Canonical t.subtrees.val[j.val]!

/-- **Assumed**, about the Solana runtime, for this transaction. -/
structure SolanaFacts (d : Deployment) (rent : Nat → U64) (tx : TxEnv) (out1 out2 : Slice U8) : Prop where
  /-- A nullifier account's rent-exempt minimum is not zero (true on Solana). -/
  nullifierRentPositive : 0 < (rent nullifierAccountSpace).val
  /-- The serialized external data fits in a vector: 120 bytes plus the two encrypted outputs
      is at most the largest `usize`. True of every real transaction (at most 1232 bytes). -/
  fitsInVector : out1.length + out2.length + 120 ≤ Usize.max
  /-- The pool's address does not sign the transaction. It is a program-derived address: it has
      no private key, and the program never signs for it. Needed when Anchor's `init` of the two
      nullifier accounts takes nothing from the signer (both addresses already hold their rent):
      then nothing else stops the signer from being the pool. -/
  poolDoesNotSign : poolAddr d ∉ tx.signers

/-- **Assumed**, about the circuit and SHA-256, for this transaction. -/
structure CryptoFacts (d : Deployment) (proof : zkcash_core.transact.Proof) : Prop where
  /-- The two input nullifiers differ. Only the circuit enforces this (spec
      `nullifiersDistinct`, a case of the circuit-soundness assumption T1). Neither the program
      nor Anchor checks it: Anchor checks `nullifier2` (the address of `nullifier0` when the two
      are equal) before creating `nullifier0`. Informational finding I1. -/
  distinctNullifiers : proof.input_nullifiers.val[0]! ≠ proof.input_nullifiers.val[1]!
  /-- SHA-256 collision resistance for the addresses of the two new nullifier accounts (slot 0
      of nullifier 0, slot 1 of nullifier 1): they are different addresses. -/
  nullifierAddressesDiffer : PdaCollisionFree d.toAddresses
    {d.pdaInput (nullifier0Seeds proof.input_nullifiers.val[0]!),
     d.pdaInput (nullifier1Seeds proof.input_nullifiers.val[1]!)}

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT]

/-- **Assumed**, about the `alt_bn128` pairing (for the verifier bridge): the spec's bilinearity
    laws (`LeanSpec.Pairing` requires them) and that pairing with `-a` gives the inverse. All
    true of the BN254 optimal ate pairing. -/
structure PairingLaws (e : G1 → G2 → GT) : Prop where
  smul_left : ∀ (s : LeanSpec.F) (a : G1) (b : G2), e (s • a) b = (e a b) ^ s.val
  smul_right : ∀ (s : LeanSpec.F) (a : G1) (b : G2), e a (s • b) = (e a b) ^ s.val
  neg_left : ∀ (a : G1) (b : G2), e (-a) b = (e a b)⁻¹

variable {s : AltBn128}

/-- The spec's pairing: the syscall's. -/
@[reducible] def syscallPairing (C : AltBn128Contracts s G1 G2 GT) (laws : PairingLaws C.e) :
    @LeanSpec.Pairing (syscallGroups C) _ _ _ _ _ :=
  @LeanSpec.Pairing.mk (syscallGroups C) _ _ _ _ _ C.e laws.smul_left laws.smul_right

end

/-! ## For handler completeness only

Safety ("code accepts ⟹ spec allows") needs only what a returned answer means. Completeness
("spec allows ⟹ code accepts") also needs the primitives to answer at all. -/

/-- **Assumed** (handler completeness only): the hash functions return a value where the
    program needs one. True of the real libraries: `light-poseidon` fails only on inputs ≥ p,
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

/-- **Assumed** (handler completeness only): the `alt_bn128` syscalls return a value on valid
    points, and the pairing answers 1 exactly when the product of the pairings is 1. The
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

/-- **Assumed** (handler completeness only): the syscalls decode the three G2 points of the
    program's verifying key. True: the trusted setup produced valid points, and the real
    program verifies real proofs on chain. Needed because
    `programKey` reads an undecodable key point as `0`, so without it the spec could accept a
    proof the code rejects. The key's G1 points are checked by computation
    (`key_alpha_decodes`, `key_ic_decodes`); the G2 decoding is a parameter of core-model's
    contracts, so it cannot be checked in Lean. -/
structure KeyG2Decodes (C : AltBn128Contracts s G1 G2 GT) : Prop where
  beta : C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_beta_g2 ≠ none
  gamma : C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_gamme_g2 ≠ none
  delta : C.decodeG2 zkcash_core.verifying_key.VERIFYING_KEY.vk_delta_g2 ≠ none

/-- **Assumed** (handler completeness only): the deployment's hashes are the spec's
    (`HashesAgree`), and its hash and syscall calls return a value on valid input. -/
structure CompletenessAssumptions (c : Crypto) (C : AltBn128Contracts c.altBn128 G1 G2 GT) : Prop where
  hashesAgree : HashesAgree c
  hashesSucceed : HashesSucceed c
  syscallsSucceed : SyscallsSucceed C
  keyDecodes : KeyG2Decodes C

end

/-- **What holds when the handler starts** (handler completeness only), in the state `s₁` after
    Anchor's checks and `init`s, for the tree and config the handler is given. -/
structure HandlerContext (a : TransactAccounts) (s₁ : State)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (config : zkcash_core.admin.GlobalConfig)
    (out1 out2 : Slice U8) : Prop where
  /-- Invariant (`WellFormed.tree`): height 26, a history of 100 roots, a root index below 100. -/
  treeShape : TreeShape tree
  /-- Invariant (`WellFormed.storedRoots`): every stored root is canonical. -/
  rootsCanonical : ∀ j : Fin 100, Canonical tree.root_history.val[j.val]!
  /-- Invariant (`WellFormed.storedSubtrees`): every stored subtree is canonical. -/
  subtreesCanonical : ∀ j : Fin 26, Canonical tree.subtrees.val[j.val]!
  /-- Invariant (`WellFormed.config`): the deposit fee rate is at most 10000. -/
  depositRate : config.deposit_fee_rate.val ≤ 10000
  /-- Invariant (`WellFormed.config`): the withdrawal fee rate is at most 10000. -/
  withdrawalRate : config.withdrawal_fee_rate.val ≤ 10000
  /-- Invariant (`WellFormed.config`): the fee error margin is at most 10000. -/
  feeMargin : config.fee_error_margin.val ≤ 10000
  /-- Premise: the signer is a plain system account. Guaranteed by Anchor whenever creating the
      two nullifier accounts takes lamports from the signer (a system transfer requires a plain
      system account as source); that is always the case unless both nullifier addresses
      already hold their rent. -/
  signerIsSystemAccount : (s₁ a.signer).owner = systemProgram ∧ (s₁ a.signer).data.isEmpty
  /-- Assumed (`SolanaFacts.fitsInVector`): the serialized external data fits in a vector. -/
  fitsInVector : out1.length + out2.length + 120 ≤ Usize.max

/-- **Outside the spec's level of detail (by design)**: Solana details the spec deliberately
    does not model. Each field rules one out; transactions where it matters are not covered. -/
structure OutsideSpecDetail (d : Deployment) (rent : Nat → U64) (s : State) (tx : TxEnv)
    (a : TransactAccounts) (proof : zkcash_core.transact.Proof) : Prop where
  /-- The rent is fixed. The spec fixes the two rent amounts; the code reads Solana's `Rent`
      sysvar each time. Ruled out: the transaction sees a different rent rate. -/
  rentFixed : tx.minimumBalance = some rent
  /-- Pre-funded nullifier addresses. Anyone can send lamports to the address of a nullifier
      account before it exists; Anchor then only tops it up, so the signer pays less than the
      spec's `2 * nullifierRent`. Ruled out: both addresses hold nothing beforehand. -/
  nullifierAddressesEmpty :
    (s (d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!))).lamports.val = 0 ∧
    (s (d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!))).lamports.val = 0
  /-- Payees that are nullifier accounts. The spec does not count nullifier accounts as public
      accounts; a payment to one (an existing one, or one this transaction creates) is locked
      there. Ruled out: neither payee is a nullifier account. -/
  payeesNotNullifierAccounts :
    (∀ b, (s a.recipient).data ≠ .nullifier b) ∧ (∀ b, (s a.feeRecipientAccount).data ≠ .nullifier b) ∧
    a.recipient ≠ d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!) ∧
    a.recipient ≠ d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!) ∧
    a.feeRecipientAccount ≠ d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!) ∧
    a.feeRecipientAccount ≠ d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!)

/-- The assumptions one step of an execution needs: `initialize` and `transact` see the rent
    `rent`; a `transact` satisfies the per-transaction assumptions (`SolanaFacts`,
    `CryptoFacts`). -/
def StepAssumptions (d : Deployment) (rent : Nat → U64) (tx : TxEnv) : Instruction → Prop
  | .initialize _ => tx.minimumBalance = some rent
  | .transact _ proof _ _ out1 out2 =>
    SolanaFacts d rent tx out1 out2 ∧ CryptoFacts d proof ∧ tx.minimumBalance = some rent
  | _ => True

/-- **Assumed**, for one execution from `s₀` with events `evs` (used by `run_connection`):
    every step of it satisfies `StepAssumptions`, and the program's three fixed accounts are
    different. -/
structure ExecutionAssumptions (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event) :
    Prop where
  /-- SHA-256 collision resistance for the program's three fixed addresses (the tree, the pool,
      the config): they are three different accounts. Same kind of assumption as
      `CryptoFacts.nullifierAddressesDiffer`. Without it, `initialize` could write two of them
      to the same account. -/
  fixedAddressesDiffer : PdaCollisionFree d.toAddresses
    {d.pdaInput merkleTreeSeeds, d.pdaInput treeTokenSeeds, d.pdaInput globalConfigSeeds}
  /-- Every program step of the execution, from the state the execution reached before it,
      satisfies `StepAssumptions`. -/
  eachStep : ∀ pre post s tx ix em, evs = pre ++ .program tx ix em :: post → Run d s₀ pre s →
    StepAssumptions d rent tx ix

end Connection
