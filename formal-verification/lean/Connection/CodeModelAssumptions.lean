import Connection.Mapping
open Aeneas Aeneas.Std Result

/-! # Assumptions about the code model

REVIEW SURFACE. What the connection theorems assume about the code side alone: the deployment,
Solana and Anchor, and the cryptographic primitives. Nothing here mentions the spec. The links
between code and spec are in `Hypotheses.lean`; core-model's own assumptions are in
`core-model/README.md`.

First the assumptions soundness needs, then those only completeness needs. Address collisions
are not assumed away (`AddressCollision.lean`).
-/

namespace Connection

/-! ## For soundness -/

/-- `ProgramNotSystem d` (assumption, about the deployment): the program is not the System Program.
    True of every deployment: nothing can be deployed at the System Program's address.
    Needed because the code treats an account owned by the System Program as free: a nullifier
    account (so no nullifier is spent twice) and the tree, pool and config (so `initialize`
    runs once). -/
def ProgramNotSystem (d : CodeModel.Deployment) : Prop := d.programId ≠ CodeModel.systemProgram

/-- `NullifiersDiffer xs`: public inputs 3 and 4 of a proof (its two input nullifiers) differ. -/
def NullifiersDiffer (xs : List (Std.Array U8 32#usize)) : Prop := xs[3]! ≠ xs[4]!

/-- `TransactAssumptions d ctx proof` (assumption, for one `transact` instruction): what we assume
    of one `transact` instruction, given its Solana transaction's context `ctx` and its proof
    `proof`. It has two parts:
    - no program-derived address signs the Solana transaction (a Solana fact);
    - the circuit gives the proof two distinct input nullifiers (an assumption about the circuit).
    `transact_connection` assumes it for its instruction, and `run_connection` for every
    `transact` instruction of the code run (`TransactAssumptionsInRun`). -/
structure TransactAssumptions (d : CodeModel.Deployment) (ctx : CodeModel.TxContext)
    (proof : CodeModel.Proof) : Prop where
  /-- No program-derived address is among the Solana transaction's signers (about Solana).
      True on Solana: a PDA is off the ed25519 curve, so it has no private key. Needed so that
      the signer is neither the pool nor a new nullifier account. -/
  pdasDoNotSign : ∀ seeds, d.pda seeds ∉ ctx.signers
  /-- If the proof verifies, its two input nullifiers differ (about
      `circuits/transaction2.circom`). Only the circuit enforces this, not the program or Anchor
      (finding I1). Spec: `RelationS.noDuplicateNullifiers` (by T0). -/
  distinctNullifiers : CodeModel.Groth16Sound d.crypto NullifiersDiffer {proof}

/-- `TransactAssumptionsInRun d events` (assumption, for a code run): `TransactAssumptions` holds
    for every `transact` instruction that the code run `events` accepted. -/
def TransactAssumptionsInRun (d : CodeModel.Deployment) (events : List CodeModel.Event) : Prop :=
  ∀ event ∈ events,                                       -- for every event of the code run,
    ∀ txEnv accounts proof extAmount fee out1 out2 emitted,
      event = .program txEnv (.transact accounts proof extAmount fee out1 out2) emitted →
                                                          -- if it is a `transact` instruction:
        TransactAssumptions d txEnv.toTxContext proof     -- these assumptions hold

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT]

/-- `PairingLaws e` (assumption, about the `alt_bn128` pairing): `e(-a, b) = e(a, b)⁻¹`. True of
    the BN254 optimal ate pairing. Needed for the verifier bridge: the code checks
    `e(-A, B) · e(α, β) · e(vkX, γ) · e(C, δ) = 1`, the spec `e(A, B) = e(α, β) · e(vkX, γ) · e(C, δ)`. -/
structure PairingLaws (e : G1 → G2 → GT) : Prop where
  neg_left : ∀ (a : G1) (b : G2), e (-a) b = (e a b)⁻¹

end

/-- `RuntimeFacts rent` (assumption, about Solana's runtime): `usize` is 64 bits, and every rent
    amount is positive. Both are fixed by the runtime, not by a Solana transaction or a chain
    state. -/
structure RuntimeFacts (rent : Nat → U64) : Prop where
  /-- `usize` is 64 bits. SOLANA FACT: the program runs on 64-bit SBF. Not provable: Aeneas's
      `Usize.max` depends on the platform running Lean. -/
  usize64 : Usize.max = 2^64 - 1
  /-- Every rent amount is positive. `rent n` is the minimum balance an account with `n` bytes of
      data must hold (Solana's rent-exempt minimum, `Rent::minimum_balance`).
      SOLANA FACT: even an account with no data must hold a positive balance (Solana counts 128
      bytes of account metadata, at a positive price). With `SameRent`, this gives core-model's
      `TxEnv.RentPositive`. -/
  rentPositive : ∀ n, 0 < (rent n).val

/-! ## For completeness only

Completeness must show that the code reaches `ok`: the cryptography returns a value, and Anchor's
checks on derived addresses pass. It also uses `RuntimeFacts` (above). -/

/-- `PoseidonSucceeds c` (assumption): Poseidon returns a value on canonical inputs.
    True of `light-poseidon`, which fails only on inputs ≥ p. Enough for the program: where it
    calls Poseidon (the Merkle append), the inputs are proved canonical, from the spec's
    `canonicalInputs` (commitments), the invariant `WellFormed` (stored subtrees), and
    `HashesAgree` (zero hashes, Poseidon outputs). SHA-256 always returns in the model. What a
    returned value is: `HashesAgree`. -/
structure PoseidonSucceeds (c : CodeModel.Crypto) : Prop where
  /-- Poseidon returns a value on canonical inputs. -/
  poseidon : ∀ a b, Canonical a → Canonical b → ∃ h, c.hasher.hash_pair a b = ok h

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [CommMonoid GT] {s : CodeModel.AltBn128}

/-- `g1At C input offset`: the G1 point in bytes `offset .. offset+63` of a syscall input, as the
    syscalls read it (the reading of core-model's `AltBn128Contracts`). -/
-- Given the syscalls' contracts `C`, a syscall input of `n` bytes, and a starting byte `offset`:
def g1At (C : CodeModel.AltBn128Contracts s G1 G2 GT) {n : Usize} (input : Std.Array U8 n)
    (offset : Nat)
    -- a proof that the 64 bytes from `offset` lie inside the input (Lean proves it with `simp`
    -- at each use, where `offset` and `n` are numbers); the result is a G1 point, or `none`:
    (h : offset + 64 ≤ n.val := by simp) : Option G1 :=
  -- cut out bytes `offset .. offset+63`, and decode them as the syscalls do.
  C.decodeG1 (CodeModel.bytesAt input offset 64#usize h)

/-- `g2At C input offset`: the G2 point in bytes `offset .. offset+127`, as the pairing syscall reads it. -/
-- Given the syscalls' contracts `C`, a syscall input of `n` bytes, and a starting byte `offset`:
def g2At (C : CodeModel.AltBn128Contracts s G1 G2 GT) {n : Usize} (input : Std.Array U8 n)
    (offset : Nat)
    -- a proof that the 128 bytes from `offset` lie inside the input (proved by `simp` at each
    -- use); the result is a G2 point, or `none`:
    (h : offset + 128 ≤ n.val := by simp) : Option G2 :=
  -- cut out bytes `offset .. offset+127`, and decode them as the pairing syscall does.
  C.decodeG2 (CodeModel.bytesAt input offset 128#usize h)

/-- `SyscallsSucceed C` (assumption): what core-model's `AltBn128Contracts` (the meaning of a
    returned value) leaves out:
    - the `alt_bn128` syscalls mul & add return a value on valid points;
    - the pairing answers 1 when the product of the pairings is 1 (the contracts give only the
      other direction).
    True of Solana's syscalls, which fail only on invalid input. -/
structure SyscallsSucceed (C : CodeModel.AltBn128Contracts s G1 G2 GT) : Prop where
  /-- Multiplication returns a value when its point (bytes 0..63) decodes; any scalar
      (bytes 64..95) is accepted. -/
  mul : ∀ input, g1At C input 0 ≠ none → ∃ out, s.multiplication input = some out
  /-- Addition returns a value when both points decode. -/
  add : ∀ input, g1At C input 0 ≠ none → g1At C input 64 ≠ none →
    ∃ out, s.addition input = some out
  /-- The pairing returns a value when its eight points decode, and that value ends in 1
      exactly when the product of the four pairings is 1. -/
  pairing : ∀ input (P₁ P₂ P₃ P₄ : G1) (Q₁ Q₂ Q₃ Q₄ : G2),
    g1At C input 0 = some P₁ → g2At C input 64 = some Q₁ →
    g1At C input 192 = some P₂ → g2At C input 256 = some Q₂ →
    g1At C input 384 = some P₃ → g2At C input 448 = some Q₃ →
    g1At C input 576 = some P₄ → g2At C input 640 = some Q₄ →
    ∃ out, s.pairing input = some out ∧
      (out.val[31]! = 1#u8 ↔ C.e P₁ Q₁ * C.e P₂ Q₂ * C.e P₃ Q₃ * C.e P₄ Q₄ = 1)

/-- `KeyG2Decodes C` (assumption): the syscalls decode the three G2 points of
    the program's verifying key.
    Why the assumption holds: the trusted setup produced valid points, and the program verifies
    proofs on chain. Needed because `programKey` reads an undecodable point as `0`, so
    the spec could accept a proof the code rejects. Not checkable in Lean: G2 decoding is a
    parameter of core-model's contracts (the G1 points are checked: `key_alpha_decodes`,
    `key_ic_decodes`). -/
structure KeyG2Decodes (C : CodeModel.AltBn128Contracts s G1 G2 GT) : Prop where
  beta : C.decodeG2 CodeModel.VERIFYING_KEY.vk_beta_g2 ≠ none
  gamma : C.decodeG2 CodeModel.VERIFYING_KEY.vk_gamme_g2 ≠ none
  delta : C.decodeG2 CodeModel.VERIFYING_KEY.vk_delta_g2 ≠ none

/-- `CryptoSucceeds c C` (assumption): the code's cryptography returns a value on valid input:
    Poseidon and SHA-256 (core-model's `Crypto`) and the `alt_bn128` syscalls
    (`AltBn128Contracts`). -/
structure CryptoSucceeds (c : CodeModel.Crypto)
    (C : CodeModel.AltBn128Contracts c.altBn128 G1 G2 GT) : Prop where
  /-- Poseidon returns a value on canonical inputs. -/
  poseidonSucceeds : PoseidonSucceeds c
  /-- SHA-256 always returns a value. -/
  sha256Succeeds : ∀ x, ∃ h, c.sha256.hash x = ok h
  /-- The `alt_bn128` syscalls return a value on points that decode, and the pairing's output
      matches the product of the pairings. -/
  syscallsSucceed : SyscallsSucceed C
  /-- The verifying key's three G2 points decode. -/
  keyDecodes : KeyG2Decodes C

end

/-- `PdasOnlyByProgram d s` (assumption, about Solana, for this chain state): only the program
    creates accounts at its derived addresses. In chain state `s`, each derived address holds either
    - an account the program created (owned by the program, with program data), or
    - no account yet (owned by the System Program, no data; it may hold lamports sent to it).

    True on Solana: creating an account (`create_account`, `allocate`, `assign`) needs the new
    address to sign. A derived address has no private key; it signs only when the program that
    derives it calls `invoke_signed` with its seeds. So only the program creates accounts there,
    and it assigns each to itself (Anchor's `init`). Anyone else can only send lamports there
    (`transfer` needs no signature from the recipient). -/
def PdasOnlyByProgram (d : CodeModel.Deployment) (s : CodeModel.State) : Prop :=
  ∀ seeds, ((s (d.pda seeds)).owner = d.programId ∧ (s (d.pda seeds)).data.isProgramData = true) ∨
    CodeModel.Initializable s (d.pda seeds)

end Connection
