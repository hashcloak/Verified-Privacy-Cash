# Findings

| ID | Title | Severity |
|---|---|---|
| L1 | Documented internal transfers are rejected | Low |
| F7 | A root can be evicted before an honest proof lands | Informational |
| I1 | Only the circuit keeps a transaction's two input nullifiers distinct | Informational |
| A0 | The verifier mixes two encodings of a curve point | Informational |

## L1. Documented internal transfers are rejected

The documentation lists internal transfers, with an external amount of zero, as a supported
transaction type, used to move, split or merge notes inside the pool. `check_public_amount`
(`utils.rs`) rejects every transaction with an external amount of zero, so these are
impossible. Every transaction must therefore deposit or withdraw, which links it to a public
account and weakens privacy.

Recommendation: accept an external amount of zero in `check_public_amount`, with the fee paid
from the pool, or remove internal transfers from the documentation.

## F7. A root can be evicted before an honest proof lands

A proof is accepted only if its Merkle root is among the last 100 roots. Each transaction
adds two roots, so a root stays valid for about 50 transactions. Anyone who sends that many
transactions while an honest user's transaction is in flight makes it fail. No funds are at
risk: the user can prove against a newer root and retry, and each blocking attempt costs the
attacker about 50 transactions.

A larger window narrows this. Note that proving against an old root reveals that the note is
older than that root, which shrinks its anonymity set.

## I1. Only the circuit keeps a transaction's two input nullifiers distinct

Neither the program nor Anchor's account checks reject a transaction whose two input
nullifiers are equal. The accounts `nullifier2` and `nullifier3` only stop a nullifier being
reused in the other slot by a later transaction: with equal nullifiers, `nullifier2` has the
address of `nullifier0`, and Anchor checks it before creating `nullifier0`. The circuit does
enforce distinct nullifiers. If it ever did not, one note could be spent twice in a single
transaction and its amount counted twice.

Recommendation: add `require!(proof.input_nullifiers[0] != proof.input_nullifiers[1])` to
`transact`, so this no longer depends on the circuit alone.

## A0. The verifier mixes two encodings of a curve point

The verifier reads the proof's 64-byte point A in two ways. The `alt_bn128` syscalls, used
for the pairing check, follow EIP-196: 64 zero bytes are the identity point. `negate_g1`
decodes A with arkworks, whose format marks the identity with a flag bit and rejects 64 zero
bytes. So a proof whose A is the identity is rejected. No valid proof is affected: an honest
prover never produces that A, and forging a valid proof with it is infeasible. Two decoders
for one format are a common source of bugs; here the stricter one runs first, so the effect
is harmless.

Recommendation: decode A in `negate_g1` with the same convention as the syscalls (map the
all-zero input to itself), or use a single decoder for both.

## Notes: behaviour the documentation should state

These are not defects. The code makes a reasonable choice that the documentation does not
mention, so users and integrators cannot know it.

- **The external amount `−2^63` is rejected.** The external amount is an `i64`, whose range
  is `−2^63` to `2^63 − 1`. Negating `−2^63` overflows, so `check_public_amount` and
  `validate_fee` reject it. This is reasonable: `2^63` lamports is about 9.2 billion SOL,
  more than the total SOL supply, so no real withdrawal is affected. Our specification
  includes this rule, but it is not in the documentation, which should state it.
- **The fee error margin is at most 100%.** `update_global_config` refuses a margin above
  10000 basis points. Our specification includes this rule, because its fee rule computes
  `10000 − margin`; the documentation gives the default (5%) but no bound, and should state it.
- **Only the admin key can initialize the pool.** `initialize` checks the caller against a
  hard-coded admin key; whoever initializes becomes the authority over fees and the deposit
  limit. In the localnet and test builds there is no admin key, so anyone can initialize.
  Our specification includes this rule; the documentation should state it, and that deployments
  must use a build with the admin key set.
