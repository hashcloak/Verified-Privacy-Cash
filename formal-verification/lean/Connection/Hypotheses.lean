import Connection.Mapping
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # The hypotheses of the connection theorem for `transact`

REVIEW SURFACE. Besides "the code model accepted the transaction", the connection theorems
(`Connection/Statements.lean`) take these hypotheses. They are of different kinds, and should
be read differently:

1. `HashesAgree` (ASSUMED, about the deployment's hash functions): the code's Poseidon, zero
   hashes and SHA-256 compute the spec's `H2`, `Z` and `sha256`.
2. `WellFormed` (INVARIANT, PROVED): facts about the program's own accounts. Proved for every
   state an execution reaches from genesis (`wellFormed_reachable`), so the main result
   (`transact_connection_main`) does not take it as a hypothesis; the per-step theorems do.
3. `SolanaFacts` (ASSUMED, about the Solana runtime): the rent is positive, and the
   transaction's data fits in memory.
4. `CryptoFacts` (ASSUMED, about the circuit and SHA-256, for this transaction): the circuit
   makes the two nullifiers differ; SHA-256 makes the two new nullifier accounts' addresses
   differ.
5. `PairingLaws` (ASSUMED, about the `alt_bn128` pairing), with core-model's syscall contracts
   `AltBn128Contracts`: needed by the verifier bridge.
6. `OutsideSpecDetail` (BY DESIGN): Solana details the spec deliberately does not model, as it
   is written at the level of the documentation. Each field rules one out; the theorem does not
   cover transactions where such a detail matters. Not a defect of the code or the spec.

No code/spec difference is currently excluded: the main theorem has no `Findings` hypothesis.
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

/-- **Invariant, proved**: facts about the program's own accounts. They hold in every state an
    execution reaches from genesis (`wellFormed_reachable`), with `spent` the nullifiers that
    execution spent. -/
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

/-- **Assumed**, about the Solana runtime, for this transaction. -/
structure SolanaFacts (rent : Nat → U64) (out1 out2 : Slice U8) : Prop where
  /-- A nullifier account's rent-exempt minimum is not zero (true on Solana). -/
  nullifierRentPositive : 0 < (rent nullifierAccountSpace).val
  /-- The serialized external data fits in a vector: 120 bytes plus the two encrypted outputs
      is at most the largest `usize`. True of every real transaction (at most 1232 bytes). -/
  fitsInVector : out1.length + out2.length + 120 ≤ Usize.max

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
    @LeanSpec.Pairing (syscallGroups G1 G2 GT) _ _ _ _ _ :=
  @LeanSpec.Pairing.mk (syscallGroups G1 G2 GT) _ _ _ _ _ C.e laws.smul_left laws.smul_right

end

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

end Connection
