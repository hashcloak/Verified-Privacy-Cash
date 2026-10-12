/**
 * Generates the Groth16 proofs the transact conformance scenarios submit,
 * with the fork's own test library (tests/lib: notes, Merkle tree, ext-data
 * hash, prover) and the circuit artifacts (artifacts/circuits/transaction2).
 * Writes proofs.json next to this file. Keys and blindings are fixed; proofs
 * are randomized by snarkjs, so the file is generated once and committed
 * (scripts/gen_proofs.sh regenerates it).
 *
 * The proofs, against the program's state as the scenarios build it:
 *   deposit       : 1_000_000 lamports into note A (two empty input notes), no fee
 *   withdraw      : note A spent in input slot 0, everything withdrawn (fee 2500)
 *   withdraw_slot1: note A spent in input slot 1 instead (same nullifier, other slot)
 */

import * as fs from 'fs';
import * as path from 'path';
import BN from 'bn.js';
import { PublicKey } from '@solana/web3.js';
import { WasmFactory } from '@lightprotocol/hasher.rs';

const FORK = process.env.FORK as string;
const lib = (m: string) => require(path.join(FORK, 'anchor/tests/lib', m));
const { Utxo } = lib('utxo');
const { Keypair } = lib('keypair');
const { MerkleTree } = lib('merkle_tree');
const { getExtDataHash } = lib('utils');
const { prove, parseProofToBytesArray, parseToBytesArray } = lib('prover');
const { FIELD_SIZE } = lib('constants');

const KEY_BASE = path.join(FORK, 'artifacts/circuits/transaction2');
const SOL_MINT = new PublicKey('11111111111111111111111111111112');
// The harness's fixed recipient and fee recipient (32 bytes of 0x0d and 0x0e).
const RECIPIENT = new PublicKey(Buffer.alloc(32, 0x0d));
const FEE_RECIPIENT = new PublicKey(Buffer.alloc(32, 0x0e));

async function main() {
  const lightWasm = await WasmFactory.getInstance();
  const key = (n: number) => new Keypair('0x' + n.toString(16).padStart(64, '0'), lightWasm);
  const note = (amount: number | string, k: number, blinding: number, index = 0) =>
    new Utxo({ lightWasm, amount, keypair: key(k), blinding, index });

  const tree = new MerkleTree(26, lightWasm);
  const out: Record<string, unknown> = {};

  async function proof(
    name: string,
    inputs: any[],
    outputs: any[],
    extAmount: BN,
    fee: BN,
    enc1: string,
    enc2: string,
  ) {
    const extData = {
      recipient: RECIPIENT,
      extAmount,
      encryptedOutput1: Buffer.from(enc1),
      encryptedOutput2: Buffer.from(enc2),
      fee,
      feeRecipient: FEE_RECIPIENT,
      mintAddress: SOL_MINT,
    };
    const publicAmount = extAmount.sub(fee).add(FIELD_SIZE).mod(FIELD_SIZE);
    const paths = inputs.map((x) =>
      x.amount.isZero()
        ? { pathElements: new Array(26).fill(0), pathIndices: 0 }
        : (() => {
            const p = tree.path(x.index);
            return { pathElements: p.pathElements, pathIndices: x.index };
          })(),
    );
    const input = {
      root: tree.root(),
      inputNullifier: await Promise.all(inputs.map((x) => x.getNullifier())),
      outputCommitment: await Promise.all(outputs.map((x) => x.getCommitment())),
      publicAmount: publicAmount.toString(),
      extDataHash: getExtDataHash(extData),
      inAmount: inputs.map((x) => x.amount.toString(10)),
      inPrivateKey: inputs.map((x) => x.keypair.privkey),
      inBlinding: inputs.map((x) => x.blinding.toString(10)),
      mintAddress: inputs[0].mintAddress,
      inPathIndices: paths.map((p) => p.pathIndices),
      inPathElements: paths.map((p) => p.pathElements),
      outAmount: outputs.map((x) => x.amount.toString(10)),
      outBlinding: outputs.map((x) => x.blinding.toString(10)),
      outPubkey: outputs.map((x) => x.keypair.pubkey),
    };
    const result = await prove(input, KEY_BASE);
    const p = parseProofToBytesArray(result.proof);
    const s = parseToBytesArray(result.publicSignals);
    out[name] = {
      proof_a: p.proofA,
      proof_b: p.proofB.flat(),
      proof_c: p.proofC,
      root: s[0],
      public_amount: s[1],
      ext_data_hash: s[2],
      input_nullifiers: [s[3], s[4]],
      output_commitments: [s[5], s[6]],
      ext_amount: extAmount.toString(),
      fee: fee.toString(),
      encrypted_output1: Buffer.from(enc1).toString('hex'),
      encrypted_output2: Buffer.from(enc2).toString('hex'),
      commitments_decimal: input.outputCommitment,
    };
    return input.outputCommitment;
  }

  // Deposit: two empty inputs; outputs note A (1_000_000) and an empty note.
  const A = note(1_000_000, 101, 11, 0);
  const deposited = await proof(
    'deposit',
    [note(0, 201, 21), note(0, 202, 22)],
    [A, note(0, 102, 12)],
    new BN(1_000_000),
    new BN(0),
    'deposit-output-1',
    'deposit-output-2',
  );
  deposited.forEach((c: string) => tree.insert(c));

  // Withdraw everything from note A (index 0), fee 2500 (withdrawal rate 25 bps).
  const fee = new BN(2500);
  const ext = fee.sub(new BN(1_000_000)); // fee + outputs - inputs
  await proof('withdraw', [A, note(0, 203, 23)], [note(0, 103, 13), note(0, 104, 14)], ext, fee,
    'withdraw-output-1', 'withdraw-output-2');
  // The same note in input slot 1.
  await proof('withdraw_slot1', [note(0, 204, 24), A], [note(0, 105, 15), note(0, 106, 16)], ext, fee,
    'withdraw1-output-1', 'withdraw1-output-2');

  fs.writeFileSync(path.join(__dirname, 'proofs.json'), JSON.stringify(out, null, 1) + '\n');
  console.log('wrote proofs.json:', Object.keys(out).join(', '));
}

main().then(() => process.exit(0), (e) => {
  console.error(e);
  process.exit(1);
});
