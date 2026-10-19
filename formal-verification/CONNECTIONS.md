# Connection theorems: status

How the extracted code model (`code_model/`) is connected to the Lean spec
(`Spec/privacy_cash_spec.lean`). Theorems live in `lean/Connection/`. Open work is tracked in
`TODO.md`, not here.

**Scope: safety.** Each connection says "if the code accepts, the spec condition holds" (and
the resulting state matches). Rejection (an `Err`, a panic, non-termination) is "no
transition" in the spec, so nothing is claimed about how the code rejects; on-chain all three
abort the instruction and the Solana runtime discards its account writes (a runtime
assumption). This is what invariant inheritance needs. Completeness (spec accepts ⟹ code
accepts) is out of scope. Because of this scope, the bare diagnostic axioms used to build
`Err` values (`alloc.string.ToString.Blanket.to_string`, `TrustedFuns.lean`) need no
property: a rejection branch can't produce `ok (.Ok _)` whatever they return
(`bindNeOkUnit`, `feeErrNeOk` in `Basic.lean`).

The spec is authoritative: where code and spec disagree, that is a finding about the code
(see the last section), not a reason to change the spec.

## Result

1. **`transactSafe`** (`TransactSafety.lean`): if `fv_transact_entry` returns
   `ok (.Ok (), …)`, then `transact (mapTxInputs …) (mapOldWorld …) (mapNewWorld …)` holds,
   and the returned tree account is still well-formed (`TreeShape`). Covers deposits and
   withdrawals, with and without a fee; `extAmt = 0` is shown unreachable. Includes
   `appendSafe`, the full 26-level Merkle `append` loop.
2. **`reachableRefines`** (`Reachable.lean`): every state reachable from the initial code
   state by `CodeStep`s (successful `fv_transact_entry` calls) satisfies `CodeInv` and maps
   to a world reachable from `initWorld`. `initRefines` is the base case.
3. **`codeInvariant`** (`Reachable.lean`): every spec invariant
   `ReachableWorld (initWorld …) w → P w` holds of every code-reachable state.
   `codeSolBalanceCorrect` instantiates it with invariant 3.

All three are `sorry`-free (checked with `#print axioms`).

## Per-precondition / per-effect theorems (`Basic.lean`)

| Spec piece | Status | Theorem | Code side |
|---|---|---|---|
| `pubAmtConsistent` | ✅ | `checkPublicAmountRefines` | `utils.fv_check_public_amount_entry` |
| `rootKnown` | ✅ | `isKnownRootRefines`, `isKnownRootSafe` | `MerkleTree.is_known_root` |
| `poolSolvent` | ✅ (under `hDevPool`) | `poolSolventRefines` | balance guards in `fv_transact_entry` |
| `signerSolvent` | ✅ | `signerSolventRefines` | `signer_lamports.checked_sub` |
| `treeHasRoom` | ✅ (under `hDevRoom`) | `treeHasRoomRefines` | `MerkleTree::append`'s room guard |
| `depositWithinLimit` | ✅ | `depositWithinLimitRefines` | deposit-limit guard |
| `feeSufficient` | ✅ | `feeSufficientRefines` | `utils.validate_fee` |
| `externalDataBound` | ✅ | `externalDataBoundRefines` | `utils.calculate_complete_ext_data_hash` |
| `proofValid` | ⬜ assumed (`hVerifySound`) | — | `utils.fv_verify_proof_full_entry` |
| `nullifiersDistinct` | ✅ derived from `proofValid` via `Deployment.soundness` | — | circuit only, no program check |
| `nullifiersFresh` | assumed (`hFresh`), runtime | — | Anchor PDA `init`, invisible to the code model |
| `transferEffects` | ✅ | `transferEffectsDepositRefines`, `transferEffectsWithdrawalRefines` | balance updates in `fv_transact_entry` |
| fee transfer in `transactEffects` | ✅ | `transactEffectsFeeRefines` | fee-transfer block |
| `appendEffects` | ✅ | `appendSafe` (`TransactSafety.lean`) | `MerkleTree.append` |
| nullifier union in `transactEffects` | runtime, modelled in `mapNewWorld` / `CodeStep` | — | Anchor PDA creation |

`appendRefines` and `fv_transact_entry_depositAcceptRefines` in `Basic.lean` are
completeness-direction results, still contain `sorry`, and are not used by the result above.

## What is assumed rather than derived

**Global** (hypotheses of `reachableRefines` / `codeInvariant`):
- Hash agreement: `hSha` (code SHA-256 = spec `Sha.sha256`), `hHashv` (code Poseidon =
  spec `H2`), and `zero_bytes` = the spec's zero ladder `Z 0..26`.
- The initial state is **hand-modelled** (`codeInitState`, transcribed from `initialize` /
  `MerkleTree::initialize`), because `initialize` isn't extracted.

**Per transaction** (premises of `CodeStep`, same as `transactSafe`'s groups):
1. the accounts passed to the code carry the world's real balances;
2. account model: recipient ≠ fee recipient (the harness can't express aliased accounts);
3. runtime: nullifiers fresh (Anchor PDA `init`);
4. verifier soundness: code verifier accepts ⟹ `proofValid` (`hVerifySound`);
5. serializer bound on the encrypted outputs (`hExtDataSum`);
6. `proof_root` is canonical (`hRootCanon`);
7. the two **code deviations** below (`hDevPool`, `hDevRoom`).

**Proven along the induction, not assumed:** tree shape (height 26, history size 100,
`root_index < 100`) and fee rates ≤ 10000 (`CodeInv`). These are hypotheses of
`transactSafe` alone, discharged in `reachableRefines`. This relies on `CodeStep` only
modelling `transact`; the config setters would need their own preservation proof.

**Inherited from the spec:** `AgreesOnProgramEffects` doesn't constrain the signer's
balance (the spec's `TODO(security gap)`), so the connection can't transfer anything about
it either.

## Findings: code is more permissive than the spec

`transactSafe` carries each as an explicit hypothesis, so invariants only transfer to code
states reached through transactions that also met the spec's stricter condition.

- **Pool solvency on deposits with a fee** (`hDevPool`). The code checks
  `pool + extAmt ≥ fee + rent` (balance *after* the deposit, `lib.rs:697`); the spec's
  `poolSolvent` requires `pool ≥ fee + rent` (balance *before*). Example: pool at exactly
  `rent`, deposit 10, fee 1: the code accepts, the spec rejects.
- **Tree capacity off by one** (`hDevRoom`). `append` accepts while `next_index < 2^26`, so
  both appends succeed for `next_index ≤ 2^26 − 2`; the spec's `treeHasRoom` requires
  `nextIndex < 2^26 − 2`, refusing the very last leaf.

Not a deviation in the safety direction, but worth noting: at `extAmt = i64::MIN` the code
rejects (`checked_neg` overflows) where `feeSufficient` can hold.
