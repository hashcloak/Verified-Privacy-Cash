import { Connection, PublicKey, SystemProgram, TransactionInstruction, Transaction } from '@solana/web3.js';
import bs58 from 'bs58';
import * as crypto from 'crypto';
import BN from 'bn.js';

const PROGRAM_ID = new PublicKey('9fhQBbumKEFuXtMBDw8AaQyAjCorLGJQiS3skWZdQyQD');
const SQUAD_VAULT_ADDRESS = new PublicKey('AWexibGxNFKTa1b5R5MN4PJr9HWnWRwf8EW9g8cLx3dM');
const connection = new Connection('https://api.mainnet-beta.solana.com', 'confirmed');

// SPL Token Mint (USDC)
const SPL_TOKEN_MINT = new PublicKey('EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v');

// New deposit limit: 1M USDC (USDC has 6 decimals, so 1M = 1_000_000 * 10^6)
const NEW_DEPOSIT_LIMIT = new BN(1_000_000_000_000);

/**
 * Generate Anchor instruction discriminator for updateDepositLimitForSplToken
 * Anchor uses the first 8 bytes of SHA256("global:update_deposit_limit_for_spl_token")
 */
function generateUpdateDepositLimitForSplTokenDiscriminator(): Buffer {
  const hash = crypto.createHash('sha256')
    .update('global:update_deposit_limit_for_spl_token')
    .digest();
  return hash.slice(0, 8);
}

/**
 * Serialize the new limit parameter as u64 (little-endian)
 */
function serializeNewLimit(limit: BN): Buffer {
  const buffer = Buffer.alloc(8);
  limit.toArrayLike(Buffer, 'le', 8).copy(buffer);
  return buffer;
}

async function generateSquadUpdateDepositLimitForSplTokenInstruction() {
  console.log('🔧 SQUAD MULTISIG SPL TOKEN DEPOSIT LIMIT UPDATE GUIDE');
  console.log('='.repeat(60));
  console.log(`Program ID: ${PROGRAM_ID.toString()}`);
  console.log(`Squad Vault: ${SQUAD_VAULT_ADDRESS.toString()}`);
  console.log(`SPL Token Mint: ${SPL_TOKEN_MINT.toString()}`);
  console.log(`New Deposit Limit: ${NEW_DEPOSIT_LIMIT.toString()} (1M USDC)`);
  console.log('');

  // Generate PDAs - for SPL tokens, the tree account is derived from ["merkle_tree", mint]
  const [treeAccount] = PublicKey.findProgramAddressSync(
    [Buffer.from('merkle_tree'), SPL_TOKEN_MINT.toBuffer()],
    PROGRAM_ID
  );

  console.log('📋 SQUAD TRANSACTION ADDRESSES:');
  console.log('');
  console.log('Tree Account (MerkleTreeAccount):');
  console.log(treeAccount.toString());
  console.log('');
  console.log('SPL Token Mint:');
  console.log(SPL_TOKEN_MINT.toString());
  console.log('');

  // Generate instruction discriminator
  const discriminator = generateUpdateDepositLimitForSplTokenDiscriminator();
  console.log('Instruction Discriminator (hex):');
  console.log(discriminator.toString('hex'));
  console.log('');

  // Serialize the new limit parameter
  const limitBytes = serializeNewLimit(NEW_DEPOSIT_LIMIT);
  console.log('New Limit Parameter (u64, little-endian, hex):');
  console.log(limitBytes.toString('hex'));
  console.log('');

  // Combine discriminator + parameter
  const instructionData = Buffer.concat([discriminator, limitBytes]);
  console.log('Complete Instruction Data (hex):');
  console.log(instructionData.toString('hex'));
  console.log('');

  // Create the update deposit limit for SPL token instruction
  // Accounts: tree_account (mut), mint, authority (signer)
  const updateInstruction = new TransactionInstruction({
    programId: PROGRAM_ID,
    keys: [
      { pubkey: treeAccount, isSigner: false, isWritable: true },
      { pubkey: SPL_TOKEN_MINT, isSigner: false, isWritable: false },
      { pubkey: SQUAD_VAULT_ADDRESS, isSigner: true, isWritable: false },
    ],
    data: instructionData,
  });

  // Create transaction
  const transaction = new Transaction();
  transaction.add(updateInstruction);
  
  // Get recent blockhash
  const { blockhash } = await connection.getLatestBlockhash();
  transaction.recentBlockhash = blockhash;
  transaction.feePayer = SQUAD_VAULT_ADDRESS;

  // Compile the message (this is what Squad expects)
  const message = transaction.compileMessage();
  
  // Serialize the message
  const messageBytes = message.serialize();
  
  // Encode as base58 (Squad format)
  const base58Message = bs58.encode(messageBytes);

  console.log('🚀 SQUAD TRANSACTION HEX (READY TO USE):');
  console.log('');
  console.log('Copy this transaction hex and paste it directly into Squad:');
  console.log('');
  console.log(base58Message);
}

// Run the script
generateSquadUpdateDepositLimitForSplTokenInstruction().catch(console.error);