import Connection.Mapping
open Aeneas Aeneas.Std Result PrivacyCash.Model

/-! # What the connection theorem assumes

REVIEW SURFACE. Besides "the code model accepted the transaction", the connection theorem
for `transact` (`Connection/Statements.lean`) takes four groups of hypotheses. They are of
different kinds:

1. `HashesAgree` (TRUSTED, about the deployment): the code's Poseidon, zero hashes and SHA-256
   compute the spec's `H2`, `Z` and `sha256`.
2. `WellFormed` (NOT TRUSTED): facts about the program's own accounts that hold right after
   `initialize` and that every instruction keeps. The theorem gives them back for the state
   after the transaction. That `initialize` and the admin instructions establish and keep
   them is still to be proved (TODO.md).
3. `Trusted` (TRUSTED, per transaction): facts about Solana or the circuit that the code model
   cannot see.
4. `Findings` (NOT ASSUMPTIONS ABOUT THE WORLD): each field rules out one known difference
   between the code and the spec, listed in CONNECTIONS.md. The theorem says nothing about
   transactions in these cases; whether each difference is acceptable is a human decision.
-/

namespace Connection

variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha]

/-- **Trusted**: the code's hash functions compute the spec's. Each is stated as "if the code's
    hash returns `h`, then `h` is the spec's hash", so nothing is claimed about inputs it rejects. -/
structure HashesAgree (c : Crypto) : Prop where
  /-- Poseidon of two tree nodes is the spec's `H2`. -/
  poseidon : ∀ a b h, c.hasher.hash_pair a b = ok h → toF h = LeanSpec.PoseidonHashes.H2 (toF a) (toF b)
  /-- The program's zero hashes are the spec's empty-subtree roots `Z 0, …, Z 26`. -/
  zeroBytes : ∃ z, c.hasher.zero_bytes = ok z ∧ ∀ i, i ≤ 26 → toF (z.val[i]!) = LeanSpec.Z i
  /-- SHA-256 is the spec's `sha256` (used for the external data hash). -/
  sha256 : ∀ x h, c.sha256.hash x = ok h → toBytes h.val = LeanSpec.Sha.sha256 (toBytes x.val)

/-- **Not trusted**: facts about the program's own accounts in a state reached from
    `initialize`. -/
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

/-- **Trusted**, per transaction: facts about Solana and the circuit that the code model
    cannot see. -/
structure Trusted (d : Deployment) (rent : Nat → U64) (tx : TxEnv)
    (proof : zkcash_core.transact.Proof) (out1 out2 : Slice U8) : Prop where
  /-- The transaction sees the rent rate the spec's world uses. The spec fixes the two rent
      amounts; the code reads Solana's `Rent` sysvar each time (TODO.md: "Solana details"). -/
  rentFixed : tx.minimumBalance = some rent
  /-- A nullifier account's rent-exempt minimum is not zero (true on Solana). -/
  nullifierRentPositive : 0 < (rent nullifierAccountSpace).val
  /-- The serialized external data fits in a vector: 120 bytes plus the two encrypted outputs
      is at most the largest `usize`. True of every real transaction (at most 1232 bytes). -/
  fitsInVector : out1.length + out2.length + 120 ≤ Usize.max
  /-- The two input nullifiers differ. Only the circuit enforces this (spec
      `nullifiersDistinct`); the program does not check it. -/
  distinctNullifiers : proof.input_nullifiers.val[0]! ≠ proof.input_nullifiers.val[1]!
  /-- SHA-256 collision resistance for the addresses of the two new nullifier accounts (slot 0
      of nullifier 0, slot 1 of nullifier 1): they are different addresses. -/
  nullifierAddressesDiffer : PdaCollisionFree d.toAddresses
    {d.pdaInput (nullifier0Seeds proof.input_nullifiers.val[0]!),
     d.pdaInput (nullifier1Seeds proof.input_nullifiers.val[1]!)}

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT]

/-- **Trusted** (for the verifier bridge): what the bridge needs of the pairing the `alt_bn128` syscall computes: the spec's
    bilinearity laws (`LeanSpec.Pairing` requires them) and that pairing with `-a` gives the
    inverse. All true of the BN254 optimal ate pairing. -/
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

/-- **Findings**: the known differences between the code and the spec. Each field rules one
    out; transactions in these cases are not covered by the theorem. CONNECTIONS.md lists them
    with their effect. -/
structure Findings (d : Deployment) (rent : Nat → U64) (s : State) (a : TransactAccounts)
    (proof : zkcash_core.transact.Proof) (extAmount : I64) (fee : U64) : Prop where
  /-- F1, CODE DEVIATION. On a deposit with a fee, the code checks the pool's balance after the
      deposit has arrived (`pool + extAmt ≥ fee + rent`); the spec's `poolSolvent` requires it
      before (`pool ≥ fee + rent`). Ruled out: the pool covers fee plus rent before the deposit. -/
  f1_poolCoversFeeBeforeDeposit : extAmount.val > 0 → fee.val > 0 →
    (s (poolAddr d)).lamports.val ≥ fee.val + (rent treeTokenAccountSpace).val
  /-- F2, SOLANA DETAIL. If the address of a new nullifier account already holds lamports
      (anyone can send them), Anchor only tops it up, so the signer pays less than the spec's
      `2 * nullifierRent`. Ruled out: both addresses are empty. -/
  f2_nullifierAddressesEmpty :
    (s (d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!))).lamports.val = 0 ∧
    (s (d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!))).lamports.val = 0
  /-- F3, SPEC PRECONDITION. The spec's `poolIsSeparate` requires the recipient and the fee
      recipient to differ from the pool; the code does not check it (in most such cases the
      runtime's lamport check rejects the transaction). Ruled out: neither payee is the pool. -/
  f3_payeesNotPool : a.recipient ≠ poolAddr d ∧ a.feeRecipientAccount ≠ poolAddr d
  /-- F4, SOLANA DETAIL. If a payee is a nullifier account (an existing one, or one this
      transaction creates), the payment is locked in it; the spec, which does not count
      nullifier accounts, says the payee receives it. Ruled out: neither payee is a nullifier
      account. -/
  f4_payeesNotNullifierAccounts :
    (∀ b, (s a.recipient).data ≠ .nullifier b) ∧ (∀ b, (s a.feeRecipientAccount).data ≠ .nullifier b) ∧
    a.recipient ≠ d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!) ∧
    a.recipient ≠ d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!) ∧
    a.feeRecipientAccount ≠ d.pda (nullifier0Seeds proof.input_nullifiers.val[0]!) ∧
    a.feeRecipientAccount ≠ d.pda (nullifier1Seeds proof.input_nullifiers.val[1]!)

end Connection
