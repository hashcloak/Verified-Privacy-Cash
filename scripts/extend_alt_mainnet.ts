import { 
  Connection, 
  Keypair, 
  PublicKey, 
  AddressLookupTableProgram,
  Transaction,
  sendAndConfirmTransaction,
} from '@solana/web3.js';
import { getAssociatedTokenAddress } from '@solana/spl-token';
import { readFileSync } from 'fs';
import * as path from 'path';

// Load user keypair from deploy-keypair.json
const anchorDirPath = path.join(__dirname, '..', 'anchor');
const deployKeypairPath = path.join(anchorDirPath, 'deploy-keypair.json');
const keypairJson = JSON.parse(readFileSync(deployKeypairPath, 'utf-8'));
const user = Keypair.fromSecretKey(Uint8Array.from(keypairJson));

const PROGRAM_ID = new PublicKey('9fhQBbumKEFuXtMBDw8AaQyAjCorLGJQiS3skWZdQyQD');
const FEE_RECIPIENT_ACCOUNT = new PublicKey('97rSMQUukMDjA7PYErccyx7ZxbHvSDaeXp2ig5BwSrTf');
const RELAYER = new PublicKey('AF8VuwCncKd5ZBnLYYnMjqh4vLch8mjqE75sFe5ZjRFW');

// USDT mint address on mainnet
const USDT_MINT = new PublicKey('Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB');

// Existing ALT to extend
const ALT_ADDRESS = new PublicKey('HEN49U2ySJ85Vc78qprSW9y6mFDhs1NczRxyppNHjofe');

// Configure connection to Solana mainnet-beta
const connection = new Connection('https://rorie-6cdtt5-fast-mainnet.helius-rpc.com', 'confirmed');

async function main() {
  console.log('Extending ALT with USDT addresses...\n');
  console.log(`ALT: ${ALT_ADDRESS.toString()}`);
  console.log(`USDT Mint: ${USDT_MINT.toString()}`);
  console.log(`Payer: ${user.publicKey.toString()}`);

  // Derive global config PDA
  const [globalConfigAccount] = PublicKey.findProgramAddressSync(
    [Buffer.from('global_config')],
    PROGRAM_ID
  );

  // Derive USDT tree account PDA
  const [usdtTreeAccount] = PublicKey.findProgramAddressSync(
    [Buffer.from('merkle_tree'), USDT_MINT.toBuffer()],
    PROGRAM_ID
  );

  // Calculate USDT token accounts (same pattern as lines 177-193 in create_alt_mainnet.ts)
  const usdtTreeAta = await getAssociatedTokenAddress(
    USDT_MINT,
    globalConfigAccount,
    true // allowOwnerOffCurve for PDA
  );

  const usdtFeeRecipientAta = await getAssociatedTokenAddress(
    USDT_MINT,
    FEE_RECIPIENT_ACCOUNT,
    true // allowOwnerOffCurve for PDA
  );

  const usdtRelayerAta = await getAssociatedTokenAddress(
    USDT_MINT,
    RELAYER,
    false // relayer is a regular account, not a PDA
  );

  const addressesToAdd = [
    usdtTreeAccount,
    USDT_MINT,
    usdtTreeAta,
    usdtFeeRecipientAta,
    usdtRelayerAta,
  ];

  console.log('\nAddresses to add:');
  console.log(`  USDT Tree Account: ${usdtTreeAccount.toString()}`);
  console.log(`  USDT Mint: ${USDT_MINT.toString()}`);
  console.log(`  USDT Tree ATA: ${usdtTreeAta.toString()}`);
  console.log(`  USDT Fee Recipient ATA: ${usdtFeeRecipientAta.toString()}`);
  console.log(`  USDT Relayer ATA: ${usdtRelayerAta.toString()}`);

  // Extend the lookup table
  const extendInstruction = AddressLookupTableProgram.extendLookupTable({
    payer: user.publicKey,
    authority: user.publicKey,
    lookupTable: ALT_ADDRESS,
    addresses: addressesToAdd,
  });

  const tx = new Transaction().add(extendInstruction);
  
  console.log('\nSending transaction...');
  const txSignature = await sendAndConfirmTransaction(connection, tx, [user]);
  
  console.log(`\nSuccess! TX: ${txSignature}`);
  console.log(`https://explorer.solana.com/tx/${txSignature}`);
}

main();

