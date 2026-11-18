import Connection.CodeModelAssumptions
import Connection.AddressCollision
open Aeneas Aeneas.Std Result

/-! # The hypotheses that link the code to the spec

REVIEW SURFACE. The connection theorems (`ConnectionTheorems.lean`) take hypotheses from three
places:
- about the spec: its trusted assumptions T0–T3 (`Spec/Statements.lean`);
- about the code alone: `CodeModelAssumptions.lean`, and core-model's own (`core-model/README.md`);
- linking the two: this file.

First the links every theorem needs, then the premises only completeness needs.

No code/spec difference and no Solana detail is excluded from `transact_connection` or
`run_connection`. G3a for the code excludes L1 and A0 by name, G3b excludes A0
(`Findings.lean`).

Relied on, though not a hypothesis: core-model's `EnvStep` lets no outside action change the
owner or data of a program account, and the program closes none. Double-spend protection rests
on it: a nullifier account, once created, stays (`core-model/PrivacyCash/Model/Execution.lean`).
-/

namespace Connection

variable [Spec.PoseidonHashes] [Spec.Sha]

/-! ## For every theorem -/

/-- `HashesAgree d` (assumption): the spec's hash functions are the program's. The spec leaves `H2`
    and `sha256` abstract; this fixes them. Poseidon is constrained only on canonical inputs
    (below `p`), the only ones the code hashes: nothing is assumed about bytes `≥ p`. -/
structure HashesAgree (d : CodeModel.Deployment) : Prop where
  /-- Poseidon of two canonical tree nodes is canonical and is the spec's `H2`. Stated only for
      canonical inputs because the code hashes nothing else: it hashes range-checked leaves and
      stored nodes, which are proved canonical (`WellFormed`).
      Why the assumption holds: `light-poseidon` computes in `ark_bn254::Fr` (modulus `p`) and
      writes canonical bytes. -/
  poseidon : ∀ a b h, Canonical a → Canonical b → d.crypto.hasher.hash_pair a b = ok h →
    Canonical h ∧ toF h = Spec.PoseidonHashes.H2 (toF a) (toF b)
  /-- The program's zero hashes `0, …, 26` are canonical and equal the spec's `Z 0, …, Z 26`.
      Why the assumption holds: they are Poseidon outputs (checked by the fork's
      `zero_bytes_are_empty_subtree_roots` test), and entry 0 is zero. -/
  zeroBytes : ∃ z, d.crypto.hasher.zero_bytes = ok z ∧
    ∀ i, i ≤ 26 → Canonical (z.val[i]!) ∧ toF (z.val[i]!) = Spec.Z i
  /-- The program's SHA-256 is the spec's `sha256` (used for the external data hash). -/
  sha256 : ∀ x h, d.crypto.sha256.hash x = ok h → toBytes h.val = Spec.Sha.sha256 (toBytes x.val)

/-- `SameRent rent sysvarRent` (assumption): the code and the spec use the same rent. The spec
    takes its rent amounts as given (`toWorld` reads them from `rent`); the code reads Solana's
    `Rent` sysvar (`sysvarRent`, the runtime's, not the sender's). Ruled out: a transaction that
    sees a different rent, or none. `transact_connection` takes it for its transaction,
    `run_connection` for every program instruction. -/
def SameRent (rent : Nat → U64) (sysvarRent : Option (Nat → U64)) : Prop := sysvarRent = some rent

/-! ## For completeness, and G3a and G3b for the code: the transaction as submitted

These describe only the transaction as submitted.
That Anchor's account checks then pass is proved, not assumed. -/

/-- `AccountsListed d a proof` (premise): the transaction lists the right accounts: the tree, the
    pool, the config, the four nullifier addresses of the proof's nullifiers, and the System
    Program. Why a premise: the spec's transaction has no account list, so the spec cannot require the
    right one. Nothing is lost: Anchor rejects a transaction that lists any other account. -/
structure AccountsListed (d : CodeModel.Deployment) (a : CodeModel.TransactAccounts)
    (proof : CodeModel.Proof) : Prop where
  /-- The tree's account (the program's `tree_account`, seed `"merkle_tree"`). -/
  tree : a.treeAccount = d.treeAddress
  /-- The pool, which the program calls `tree_token_account` (seed `"tree_token"`). -/
  pool : a.treeTokenAccount = d.poolAddress
  /-- The config (the program's `global_config`, seed `"global_config"`). -/
  config : a.globalConfig = d.configAddress
  /-- Nullifier 0's new account (slot 0). -/
  nullifier0 : a.nullifier0 = d.pda (CodeModel.nullifier0Seeds proof.input_nullifiers.val[0]!)
  /-- Nullifier 1's new account (slot 1). -/
  nullifier1 : a.nullifier1 = d.pda (CodeModel.nullifier1Seeds proof.input_nullifiers.val[1]!)
  /-- Nullifier 1's other slot (slot 0); Anchor checks it is unused. -/
  nullifier2 : a.nullifier2 = d.pda (CodeModel.nullifier0Seeds proof.input_nullifiers.val[1]!)
  /-- Nullifier 0's other slot (slot 1); Anchor checks it is unused. -/
  nullifier3 : a.nullifier3 = d.pda (CodeModel.nullifier1Seeds proof.input_nullifiers.val[0]!)
  /-- The System Program, which `init` calls to create the nullifier accounts. -/
  systemProg : a.systemProgram = CodeModel.systemProgram

/-- `SignerIsPlain s a` (by design: not modelled in the spec): the signer is owned by the System
    Program and holds no data. On Solana only such an account can pay; the spec does not model
    account owners.

    The signer pays (deposit, nullifier rent) by System Program transfer, which requires exactly
    this (`systemTransferBalances`). This premise is not needed when the signer pays nothing (a
    withdrawal whose nullifier addresses already hold the rent). The code accepts those
    transactions anyway, so excluding them hides no difference. -/
def SignerIsPlain (s : CodeModel.State) (a : CodeModel.TransactAccounts) : Prop :=
  -- plain: owned by the System Program (only the owner may debit) and holding no data
  (s a.signer).owner = CodeModel.systemProgram ∧ (s a.signer).data.isEmpty

/-- `ReachesProgram d s a proof`: what G3a and G3b for the code take about the transaction as the
    honest owner submits it. With these, `SameRent` and the spec's preconditions, Anchor's account
    checks pass (proved in `transact_complete_except_L1_A0`, which takes the same conditions). -/
structure ReachesProgram (d : CodeModel.Deployment) (s : CodeModel.State)
    (a : CodeModel.TransactAccounts) (proof : CodeModel.Proof) : Prop where
  /-- The transaction lists the right accounts. -/
  accounts : AccountsListed d a proof
  /-- The signer is a plain system account. -/
  signerPlain : SignerIsPlain s a

end Connection
