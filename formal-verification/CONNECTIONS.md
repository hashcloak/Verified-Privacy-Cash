# Connection: code model ↔ spec

`lean/Connection/` connects the code model (`core-model/`: the extracted `zkcash_core` plus the
hand-written Solana/Anchor model) to the spec (`lean/Spec/`). Open work is in `TODO.md`.

**Review surface** (three files; proofs in `Connection/Proofs/` are not for review):
- `Mapping.lean`: how code values map to spec values (`toF`, `toPubkey`, `toTree`, `toWorld`, `toInputs`).
- `Assumptions.lean`: the hypotheses, in four groups (trusted / invariant / trusted / findings).
- `Statements.lean`: the theorems, each a commuting square (SymCrypt style): run one code
  function, map inputs and result, compare with the spec.

**Scope: safety.** Code accepts ⟹ spec allows, with the spec's effects. Wrong rejections are
not caught, so G3a/G3b do not transfer yet.

## Theorems (`Statements.lean`)

| Code | Spec | Hypotheses |
|---|---|---|
| `check_public_amount` | `pubAmtConsistent` (equal) | none |
| `is_known_root` | `rootKnown` (equal) | tree shape; canonical root and history |
| `validate_fee` | `feeSufficient` (iff, plus `extAmt ≠ i64::MIN`) | rates ≤ 100% |
| `calculate_complete_ext_data_hash` | hashes exactly `serealizeExternalData`; `none` iff not `encOutsFit` | fits in a vector |
| `append` | `appendEffects` (if it returns) / `MerkleTreeFull` (no room) | `HashesAgree`, tree shape |
| `verify_proof` | the 7 public inputs are canonical | none |
| `verify_proof` (verifier bridge) | `proofValid` (spec's `Groth16.verify`) | syscall contracts, `PairingLaws` |
| **`step … transact`** (`transact_connection_verified`, main result) | `transact` (all preconditions, exact effects) and `WellFormed` again | the four groups + syscall contracts + `PairingLaws` |

`transact_connection` is the same result for any spec instances, with the bridge replaced by a
hypothesis `hProofValid`.

All are `sorry`-free and use only Lean's standard axioms.

## Findings (excluded by `Findings`; humans decide)

- **F1, code deviation:** on a deposit with a fee, the code checks the pool after the deposit
  (`pool + extAmt ≥ fee + rent`); the spec checks before.
- **F2, Solana detail:** a pre-funded nullifier address is only topped up, so the signer pays
  less than `2 * nullifierRent`. Not a security issue (Anchor 0.31.1).
- **F3, spec precondition:** a payee may be the pool (`poolIsSeparate`). The code doesn't
  check; the lamport check rejects most such cases, two are harmless.
- **F4, Solana detail:** a payee that is a nullifier account (old or new) gets the payment
  locked there; the spec says the payee receives it.

Also: `extAmt = i64::MIN` is rejected by `validate_fee` where `feeSufficient` can hold
(harmless: `check_public_amount` rejects it first).

## Assumed, not derived

- `HashesAgree`: Poseidon, zero hashes, SHA-256 are the spec's.
- `Trusted`: rent fixed and positive; data fits in a vector; distinct nullifiers (circuit
  only); the two new nullifier addresses differ (SHA-256).
- Verifier bridge: core-model's syscall contracts (`AltBn128Contracts`), and `PairingLaws`
  (the pairing is bilinear, and pairing with `-a` inverts). The spec's groups, pairing and key
  are instantiated from these and the program's key.
- `WellFormed`: not trusted, but not yet proved for `initialize` and the admin instructions.
