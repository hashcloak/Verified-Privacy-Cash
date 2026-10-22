# core-model: a Lean model of the Privacy Cash program (SOL)

A Lean 4 model of the Privacy Cash Solana program, for proving its protocol
properties (no double spend, solvency, only the admin changes fees and limits,
and agreement with the protocol specification in `../lean/Spec/`).

**Scope: the SOL instructions** (`initialize`, `update_deposit_limit`,
`update_global_config`, `transact`). The SPL instructions are not modelled;
theorems about executions (`Run`) assume they are not called (see
[Assumptions](#assumptions)).

## How the model is built

The program is the fork in `../../privacy-cash` (a submodule). There, every
decision the program makes was moved into an Anchor-free crate,
`anchor/crates/zkcash_core`, which the program calls; the fork's tests show it
behaves exactly like upstream Privacy Cash (see [Checks](#checks)).

| Part | Files | How it is obtained |
|---|---|---|
| The program's logic | `PrivacyCash/Extracted/` | **extracted** from `zkcash_core` by Charon + Aeneas (`scripts/extract.sh`); never edited by hand |
| What Solana and Anchor do around it | `PrivacyCash/Model/{Basic,Pda,Accounts,Runtime,Program,Execution}.lean` | **hand-written**: accounts, PDAs, Anchor's account checks and `init`, lamports and the system program, and executions (`step`, `Run`) |
| Arkworks code inside the program | `PrivacyCash/Model/{Field,Bn254}.lean` | **hand-written definitions**: the scalar field as `ZMod r`, G1 negation |
| What the validator computes | `PrivacyCash/Model/{Crypto,Bn254}.lean` | **parameters**: Poseidon, SHA-256 and the `alt_bn128` syscalls; what a theorem needs of them is a hypothesis it takes. How the syscalls read a G1 point is defined (`syscallDecodeG1`) |
| One Rust library function | `PrivacyCash/Extracted/FunsExternal.lean` | hand-written `i64::checked_neg`, **proven** to match Rust (`Proofs/FunsExternal.lean`) |

`step d s tx ix` runs one instruction: `.ok (s', events)` or `.error e`.
`Run d s events s'` is an execution: program instructions and anything else
the chain allows (`EnvStep`). Everything is computable, so the model can be
run on concrete inputs.

## Checks

Each hand-written part is checked against the real program. Every check
below fails the build (or the script) on a mismatch; each was tested by
planting bugs.

| Check | What it compares | Run by |
|---|---|---|
| `Model/IdlCheck.lean` (theorems) | each instruction's accounts: order, signers, fixed addresses, PDA seeds, `has_one`; the event's fields | `lake build` |
| `Model/InterfaceCheck.lean` (build-time meta-program) | instruction arguments, account data layouts, `Proof`, error codes: read from the model's own definitions | `lake build` |
| `scripts/check_idl.sh` | the fork's IDL is byte-identical to upstream's; `Model/Idl.lean` is generated from it and current | script |
| `Tests/Conformance.lean` (traces: `Tests/ConformanceTraces.lean`, generated) | **the model's `step` against the compiled program** (mainnet build, in LiteSVM): 220 scenarios: each Anchor check of each admin account, argument boundaries, `init` funding paths, 150 random admin scenarios, and `transact` with real Groth16 proofs: deposits (with and without a fee, at the deposit limit), withdrawals, double spends, the solvency thresholds of withdrawals and of deposit fees (including a pool between withdraw + fee + rent(0) and + rent(41)), recipients that alias the fee recipient, the signer or the pool, a full tree and a wrapping root history. This is the only check of the handler's wiring (which accounts `transact` is given, in which order): the model's `step` writes that call by hand | `lake build`; traces from `scripts/check_conformance.sh` |
| `Tests/FieldVectors.lean`, `Tests/Bn254Vectors.lean` | the field (`ZMod r`) and G1 negation against arkworks, on edge-case and random inputs | `lake build`; vectors from `scripts/check_vectors.sh` |
| `Tests/G1DecodeVectors.lean` | how the syscalls read a G1 point (`syscallDecodeG1`) against solana-bn254 | same |
| `scripts/check_vk_circuit.sh` | the program's verifying key is the key of the circuit's proving key (`artifacts/circuits/transaction2.zkey`), byte for byte | script (snarkjs) |
| `Tests/AccountSpaces.lean` | the account sizes used for rent against `8 + size_of::<T>()` | same |
| `Tests/Executable.lean` | the model runs (toy deployment) | `lake build` |
| `Tests/Axioms.lean` | no theorem relies on an axiom beyond Lean's standard three | `lake build` |
| the fork's Rust tests | `zkcash_core` against upstream's code, copied verbatim as oracles (differential property tests, including the withdrawal-solvency and deposit-limit thresholds), the program's `SolTransactRuntime` over hand-built accounts (which account each lamport read and write uses; rent measured on the tree token account), the verifying key, `zero_bytes`. They do not run the `transact` handler itself, so its argument wiring is covered by the conformance traces only | `cargo test -p zkcash -p zkcash_core` |

CI (`.github/workflows/formal-verification.yml`) runs all of the above.
Re-extraction (`scripts/extract.sh`, then `git diff PrivacyCash/Extracted`)
needs Charon and Aeneas at the pinned revisions and is run by hand.

## Assumptions

What the proofs rely on without proof. Each is stated where it is used.

**Trusted tools.** rustc, Charon and Aeneas (extraction), the Aeneas Lean
library, Lean's kernel, Mathlib.

**Solana and Anchor.** The hand-written model of Anchor 0.31.1 and the Solana
runtime. It is checked by the conformance scenarios, not proven. It may accept
more than Solana does, never less: it does not model writable flags, the
rent-exemption rule for changed accounts, compute or transaction-size limits,
or the runtime's "only the owner may debit" rule. That is sound for safety
properties (anything Solana allows, the model allows) but not for liveness ones.
Which Anchor check rejects an account is not modelled (`.accounts`).

**Cryptography** (hypotheses a theorem takes, never axioms; see
`Model/Crypto.lean`, `Model/Bn254.lean`, `Model/Pda.lean`):
- Groth16 soundness for the program's key (`Groth16EquationSound`): a proof
  whose points satisfy the Groth16 equation proves the circuit's statement.
  The model's `Groth16Sound` ("the verifier accepts ⇒ the statement") is
  derived from it, since the verifier is proven to check the equation;
- the circuit (`circuits/transaction2.circom`) enforces the protocol's
  relation. Nothing here checks the circuit itself;
- `PoseidonCollisionFree`, `ExtDataHashCollisionFree`, `PdaCollisionFree`:
  no collisions among the inputs an execution uses;
- `AltBn128Contracts`: what a successful `alt_bn128` syscall computes (scalar
  multiplication, addition, the four-pairing product), over abstract groups
  that the syscall's concrete point decoding embeds into;
- `ZeroBytesConsistent`: the empty-subtree roots chain (true of the program's
  Poseidon; checked by the fork's `zero_bytes_are_empty_subtree_roots`).

No theorem relies on an axiom beyond Lean's standard `propext`,
`Classical.choice` and `Quot.sound` (`Tests/Axioms.lean` checks every one).

**Deployment.**
- The model is of the fork. Its link to upstream Privacy Cash is the
  equivalence evidence above (differential tests, identical IDL, upstream's
  integration suites).
- That the deployed program is built from upstream's source has not been
  checked (`solana-verify`).
- The program's upgrade authority is outside the model.
- The deployment's addresses, PDA derivation and `ADMIN_PUBKEY` are parameters
  (`Deployment`): theorems hold for every deployment.

**Scope.** SOL only. `transact_spl` creates nullifier accounts with the same
seeds as `transact`; until the SPL instructions are modelled, `Run` theorems
assume they are not called.

## Proven so far

- **L1** (`Proofs/Ownership.lean`): once the program owns an account it owns
  it forever, along any execution.
- Access control (`Model/Program.lean`): `update_deposit_limit` and
  `update_global_config` succeed only when signed by the authority stored in
  the tree or config they change.
- **The Groth16 verifier** (`Proofs/Groth16.lean`, adapted from
  `../lean/proofs/VerifyProof`): if the program's verifier accepts a proof,
  its public inputs are below r and `e(-A, B) · e(vk_x, γ) · e(C, δ) · e(α, β) = 1`
  for the program's key, with A the point in `proof_a`. Along the way: the
  field-size check is the numeric comparison with r, the key's modulus
  constant is r, and decoding what `negate_g1` returns gives `-A`
  (`Proofs/G1.lean`).
- `checked_neg` matches Rust (`Proofs/FunsExternal.lean`).

## Building and checking

```bash
lake exe cache get          # Mathlib build cache
lake build                  # model, proofs, and the Lean checks
./scripts/check_idl.sh      # needs anchor-cli
./scripts/check_vectors.sh  # needs cargo
./scripts/check_conformance.sh   # needs cargo-build-sbf (Solana 2.2); after check_idl.sh
./scripts/check_vk_circuit.sh    # needs snarkjs (the fork's, or npx)
```

`scripts/gen_proofs.sh` regenerates the conformance proofs (only when the
circuit, the verifying key or the `transact` scenarios change).

## Relation to `../lean/`

`../lean/` is an earlier model (`fv_*` transcriptions of a copy of the program
that is no longer in this repository, on another Aeneas revision). Its
verifier proof (`proofs/VerifyProof`) is superseded by `Proofs/Groth16.lean`;
its protocol specification (`Spec/`) is to be moved here.
