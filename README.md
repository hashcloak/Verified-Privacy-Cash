# Verified-Privacy-Cash

Formal Verification for the Privacy Cash Protocol.

This repository holds the Privacy Cash Solana program together with a machine-checked
Lean 4 model of it, extracted from the real Rust source via
[Charon](https://github.com/AeneasVerif/charon) and [Aeneas](https://github.com/AeneasVerif/aeneas).

## Formal verification

Everything related to the model lives in [`formal-verification/`](formal-verification/):

- `extract.sh` — the end-to-end pipeline: Rust → Charon (`.llbc`) → Aeneas → Lean.
- `transact_shim.llbc`, `check_public_amount_shim.llbc` — the extracted LLBC.
- `lean/TransactShim/`, `lean/CheckPublicAmountShim/` — the generated Lean model.
- `lean/Spec/` — hand-written proofs stated against that model.
- `MODEL_REPORT.md` — what extracted, the technique, and what is still open.

Status:

- **`transact`** (the core deposit/withdrawal instruction) extracts and translates completely:
  12/12 real functions transparent, 71/71 trusted primitives opaque, no errors and no
  `sorry`/`admit` in the output. This is a *model* of the instruction — generated and
  inspected, not yet proved against a specification.
- **`check_public_amount`** is proved: `deposit_spec` and `withdrawal_spec` in
  `lean/Spec/CheckPublicAmount.lean` cover both branches.

Field arithmetic over `ark-bn254`'s `Fr` is abstracted behind a shim type (`FrShim`), because
Charon cannot translate `ark-ff`'s const-generic `BigInt<N>` hierarchy. The trust boundaries
this introduces are spelled out in `MODEL_REPORT.md`.

Environment setup and reproduction steps are in [`SETUP.md`](SETUP.md).

---

# Privacy Cash

Transfer SOL privately. Private SPL tokens transfer and private swap will soon follow.

The program is fully audited by Accretion, HashCloak, Zigtur and Kriko, and verified onchain (with hash c6f1e5336f2068dc1c1e1c64e92e3d8495b8df79f78011e2620af60aa43090c5).

## Overview

This project implements a privacy protocol on Solana that allows users to:

1. **Shield SOL**: Deposit SOL into a privacy pool, generating a commitment that is added to a Merkle tree.
2. **Withdraw SOL**: Withdraw SOL from the privacy pool to any recipient address using zero-knowledge proofs.

The implementation uses zero-knowledge proofs to ensure that withdrawals cannot be linked to deposits, providing privacy for Solana transactions.

## Project Structure

- **program/**: Solana on-chain program (smart contract)
  - **src/**: Rust source code for the program
  - **test/**: Tests
  - **Cargo.toml**: Rust dependencies and configuration

## Prerequisites

- Solana CLI 2.1.18 or later
- Rust 1.79.0 or compatible version
- Anchor 0.31.1
- Node.js 16 or later
- npm or yarn
- Circom v2.2.2 https://docs.circom.io/getting-started/installation/#installing-dependencies

## SDK
If you want to integrate Privacy Cash into your project, use the [Privacy Cash SDK](https://github.com/Privacy-Cash/privacy-cash-sdk) here.

## Anchor Program
1. Navigate to the program directory:
   ```bash
   cd anchor
   ```

2. Build the program:
   ```bash
   anchor build
   ```

3. Run unit test:
   ```bash
   cargo test
   ```

4. Run integration test:
   ```bash
   npm run test:sol
   npm run test:spl
   npm run test:mint-checked
   ```

5. Deploy the program to devnet:
   ```bash
   anchor build -- --features devnet
   rm target/deploy/zkcash-keypair.json
   cp zkcash-keypair.json target/deploy/zkcash-keypair.json
   anchor deploy --provider.cluster devnet

   or
   rm target
   anchor build --verifiable
   cp zkcash-keypair.json target/deploy/zkcash-keypair.json
   anchor deploy --verifiable --provider.cluster devnet

   or
   solana program deploy target/deploy/zkcash.so --program-id zkcash-keypair.json --upgrade-authority ./deploy-keypair.json
   ```

6. Deploy to mainnet:
   ```bash
   anchor build --verifiable

   rm target/deploy/zkcash-keypair.json
   cp zkcash-keypair.json target/deploy/zkcash-keypair.json 

   anchor deploy --verifiable --provider.cluster mainnet
   ```

7. Transfer the authority to multisig wallet
   ```bash
   solana program set-upgrade-authority 9fhQBbumKEFuXtMBDw8AaQyAjCorLGJQiS3skWZdQyQD \
   --new-upgrade-authority AWexibGxNFKTa1b5R5MN4PJr9HWnWRwf8EW9g8cLx3dM \
   --upgrade-authority deploy-keypair.json \
   --skip-new-upgrade-authority-signer-check \
   --url mainnet-beta
   ```
