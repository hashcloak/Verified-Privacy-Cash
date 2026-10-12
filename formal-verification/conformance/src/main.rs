//! Conformance traces: runs the compiled zkcash program (the mainnet build) in
//! LiteSVM on fixed scenarios and prints, as Lean, what happened: the accounts
//! of each instruction before and after, the events it emitted, or how it
//! failed. `core-model/Tests/Conformance.lean` runs the Lean model's `step` on
//! the same inputs and checks it agrees (`scripts/check_conformance.sh`).
//!
//! The scenarios are a fixed list (each Anchor check of each account, the
//! boundary values of each argument, the `init` funding paths) followed by a
//! batch of random ones from a fixed seed (random account states, account
//! choices, signers and arguments), so the traces are reproducible.
//!
//! The harness is a client of the program, independent of its Rust crates:
//! it encodes instructions itself (Anchor discriminator + Borsh) and decodes
//! accounts itself. Both are checked: the discriminators against the IDL, and
//! every decoded account by re-encoding it to exactly its bytes.
//!
//! `transact` scenarios submit real Groth16 proofs (proofs/proofs.json, made
//! by proofs/gen_proofs.ts with the program's circuit). The crypto answers the
//! model needs for them are recorded by `replay`.
//!
//! Usage: conformance <zkcash.so> <idl.json> <proofs.json>

mod replay;

use base64::Engine;
use litesvm::LiteSVM;
use sha2::{Digest, Sha256};
use solana_account::Account;
use solana_instruction::{AccountMeta, Instruction};
use solana_keypair::Keypair;
use solana_message::Message;
use solana_pubkey::Pubkey;
use solana_signer::Signer;
use solana_transaction::Transaction;
use solana_transaction_error::TransactionError;
use std::collections::BTreeMap;
use std::str::FromStr;

const PROGRAM_ID: &str = "9fhQBbumKEFuXtMBDw8AaQyAjCorLGJQiS3skWZdQyQD";
/// `ADMIN_PUBKEY` of the mainnet build.
const ADMIN: &str = "AWexibGxNFKTa1b5R5MN4PJr9HWnWRwf8EW9g8cLx3dM";
const SYSTEM_PROGRAM: Pubkey = Pubkey::new_from_array([0; 32]);
const SOL: u64 = 1_000_000_000;

fn program_id() -> Pubkey {
    Pubkey::from_str(PROGRAM_ID).unwrap()
}

// ---------------------------------------------------------------------------
// Encoding (Anchor + Borsh)

/// Anchor's discriminator: the first 8 bytes of SHA-256(`namespace:name`).
fn discriminator(namespace: &str, name: &str) -> [u8; 8] {
    let h = Sha256::digest(format!("{namespace}:{name}").as_bytes());
    h[..8].try_into().unwrap()
}

fn borsh_option_u16(out: &mut Vec<u8>, v: Option<u16>) {
    match v {
        None => out.push(0),
        Some(x) => {
            out.push(1);
            out.extend_from_slice(&x.to_le_bytes());
        }
    }
}

// ---------------------------------------------------------------------------
// Accounts as the model sees them

/// `MerkleTreeAccount` (zero-copy, `repr(C)`; offsets as asserted in lib.rs).
#[derive(Clone)]
struct Tree {
    authority: [u8; 32],
    next_index: u64,
    subtrees: Vec<[u8; 32]>,
    root: [u8; 32],
    root_history: Vec<[u8; 32]>,
    root_index: u64,
    max_deposit_amount: u64,
    height: u8,
    root_history_size: u8,
    bump: u8,
    padding: [u8; 5],
}

/// An account's data, decoded the way the model's `AccountData` is.
#[derive(Clone)]
enum Data {
    Empty,
    Foreign,
    Tree(Box<Tree>),
    TreeToken { authority: [u8; 32], bump: u8 },
    GlobalConfig { authority: [u8; 32], deposit: u16, withdrawal: u16, margin: u16, bump: u8 },
    Nullifier { bump: u8 },
}

fn arr<const N: usize>(b: &[u8], at: usize) -> [u8; N] {
    b[at..at + N].try_into().unwrap()
}

fn u64_at(b: &[u8], at: usize) -> u64 {
    u64::from_le_bytes(arr(b, at))
}

fn u16_at(b: &[u8], at: usize) -> u16 {
    u16::from_le_bytes(arr(b, at))
}

/// Encodes `d` as the program stores it, padded with zeros to `len` bytes.
fn encode(d: &Data, len: usize) -> Vec<u8> {
    let mut out = Vec::new();
    match d {
        Data::Empty | Data::Foreign => unreachable!(),
        Data::Tree(t) => {
            out.extend_from_slice(&discriminator("account", "MerkleTreeAccount"));
            out.extend_from_slice(&t.authority);
            out.extend_from_slice(&t.next_index.to_le_bytes());
            t.subtrees.iter().for_each(|s| out.extend_from_slice(s));
            out.extend_from_slice(&t.root);
            t.root_history.iter().for_each(|r| out.extend_from_slice(r));
            out.extend_from_slice(&t.root_index.to_le_bytes());
            out.extend_from_slice(&t.max_deposit_amount.to_le_bytes());
            out.extend_from_slice(&[t.height, t.root_history_size, t.bump]);
            out.extend_from_slice(&t.padding);
        }
        Data::TreeToken { authority, bump } => {
            out.extend_from_slice(&discriminator("account", "TreeTokenAccount"));
            out.extend_from_slice(authority);
            out.push(*bump);
        }
        Data::GlobalConfig { authority, deposit, withdrawal, margin, bump } => {
            out.extend_from_slice(&discriminator("account", "GlobalConfig"));
            out.extend_from_slice(authority);
            out.extend_from_slice(&deposit.to_le_bytes());
            out.extend_from_slice(&withdrawal.to_le_bytes());
            out.extend_from_slice(&margin.to_le_bytes());
            out.push(*bump);
        }
        Data::Nullifier { bump } => {
            out.extend_from_slice(&discriminator("account", "NullifierAccount"));
            out.push(*bump);
        }
    }
    assert!(out.len() <= len, "encoding longer than the account");
    out.resize(len, 0);
    out
}

/// Decodes an account's data; panics unless re-encoding gives back exactly its bytes.
fn decode(owner: &Pubkey, data: &[u8]) -> Data {
    if data.is_empty() {
        return Data::Empty;
    }
    if *owner != program_id() {
        return Data::Foreign;
    }
    let disc: [u8; 8] = arr(data, 0);
    let b = &data[8..];
    let d = if disc == discriminator("account", "MerkleTreeAccount") {
        Data::Tree(Box::new(Tree {
            authority: arr(b, 0),
            next_index: u64_at(b, 32),
            subtrees: (0..26).map(|i| arr(b, 40 + 32 * i)).collect(),
            root: arr(b, 872),
            root_history: (0..100).map(|i| arr(b, 904 + 32 * i)).collect(),
            root_index: u64_at(b, 4104),
            max_deposit_amount: u64_at(b, 4112),
            height: b[4120],
            root_history_size: b[4121],
            bump: b[4122],
            padding: arr(b, 4123),
        }))
    } else if disc == discriminator("account", "TreeTokenAccount") {
        Data::TreeToken { authority: arr(b, 0), bump: b[32] }
    } else if disc == discriminator("account", "GlobalConfig") {
        Data::GlobalConfig {
            authority: arr(b, 0),
            deposit: u16_at(b, 32),
            withdrawal: u16_at(b, 34),
            margin: u16_at(b, 36),
            bump: b[38],
        }
    } else if disc == discriminator("account", "NullifierAccount") {
        Data::Nullifier { bump: b[0] }
    } else {
        panic!("program-owned account with unknown discriminator {disc:?}");
    };
    assert_eq!(encode(&d, data.len()), data, "account does not re-encode to its bytes");
    d
}

// ---------------------------------------------------------------------------
// Printing Lean

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn lean_hex(b: &[u8]) -> String {
    format!("\"{}\"", hex(b))
}

fn lean_hex_list(v: &[[u8; 32]]) -> String {
    let items: Vec<String> = v.iter().map(|x| lean_hex(x)).collect();
    format!("[{}]", items.join(", "))
}

/// Names for the keys a trace mentions (`keyName` in Lean), and the program's
/// empty-tree subtrees (printed as `zeroSubtrees`, to keep the traces short).
struct Keys(Vec<(String, Pubkey)>, Vec<[u8; 32]>);

impl Keys {
    fn name(&self, k: &Pubkey) -> String {
        match self.0.iter().find(|(_, p)| p == k) {
            Some((n, _)) => n.clone(),
            None => format!("(pk {})", lean_hex(k.as_ref())),
        }
    }
}

/// A list of 32-byte entries as runs of equal entries: `rle [("hex", count), ..]`.
fn lean_rle(v: &[[u8; 32]]) -> String {
    let mut runs: Vec<([u8; 32], usize)> = Vec::new();
    for x in v {
        match runs.last_mut() {
            Some((y, n)) if y == x => *n += 1,
            _ => runs.push((*x, 1)),
        }
    }
    let items: Vec<String> = runs.iter().map(|(x, n)| format!("({}, {n})", lean_hex(x))).collect();
    format!("(rle [{}])", items.join(", "))
}

fn lean_data(d: &Data, keys: &Keys) -> String {
    match d {
        Data::Empty => ".empty".into(),
        Data::Foreign => ".foreign".into(),
        Data::Tree(t) => format!(
            "(.treeAccount (tree {} {} {} {} {} {} {} {} {} {} {}))",
            keys.name(&Pubkey::new_from_array(t.authority)),
            t.next_index,
            if t.subtrees == keys.1 { "zeroSubtrees".to_string() } else { lean_rle(&t.subtrees) },
            lean_hex(&t.root),
            lean_rle(&t.root_history),
            t.root_index,
            t.max_deposit_amount,
            t.height,
            t.root_history_size,
            t.bump,
            lean_hex(&t.padding)
        ),
        Data::TreeToken { authority, bump } => {
            format!("(.treeToken (treeToken {} {}))", keys.name(&Pubkey::new_from_array(*authority)), bump)
        }
        Data::GlobalConfig { authority, deposit, withdrawal, margin, bump } => format!(
            "(.globalConfig (globalConfig {} {} {} {} {}))",
            keys.name(&Pubkey::new_from_array(*authority)),
            deposit,
            withdrawal,
            margin,
            bump
        ),
        Data::Nullifier { bump } => format!("(.nullifier (byte {bump}))"),
    }
}

fn lean_account(a: &Option<Account>, keys: &Keys) -> String {
    match a {
        None => "Account.default".into(),
        Some(a) => format!(
            "(acct {} {} {})",
            a.lamports,
            keys.name(&a.owner),
            lean_data(&decode(&a.owner, &a.data), keys)
        ),
    }
}

fn lean_opt_u16(v: Option<u16>) -> String {
    match v {
        None => "none".into(),
        Some(x) => format!("(some {x})"),
    }
}

// ---------------------------------------------------------------------------
// Instructions

/// The accounts of `initialize`, and whether the authority signs.
#[derive(Clone)]
struct Init {
    tree: Pubkey,
    token: Pubkey,
    config: Pubkey,
    authority: Pubkey,
    system: Pubkey,
    signs: bool,
}

/// The accounts and arguments of `transact`, and whether the signer signs.
#[derive(Clone)]
struct Tx {
    tree: Pubkey,
    n0: Pubkey,
    n1: Pubkey,
    n2: Pubkey,
    n3: Pubkey,
    token: Pubkey,
    config: Pubkey,
    recipient: Pubkey,
    fee_recipient: Pubkey,
    signer: Pubkey,
    system: Pubkey,
    signs: bool,
    proof: zkcash_core::transact::Proof,
    ext_amount: i64,
    fee: u64,
    out1: Vec<u8>,
    out2: Vec<u8>,
}

/// The SOL instructions. `signs` is whether the authority (or signer) signs.
#[derive(Clone)]
enum Ix {
    Initialize(Init),
    Transact(Box<Tx>),
    UpdateDepositLimit { tree: Pubkey, authority: Pubkey, signs: bool, new_limit: u64 },
    UpdateGlobalConfig { config: Pubkey, authority: Pubkey, signs: bool, dep: Option<u16>, wd: Option<u16>, margin: Option<u16> },
}

impl Ix {
    fn instruction(&self) -> Instruction {
        let w = AccountMeta::new;
        let r = AccountMeta::new_readonly;
        let (name, accounts, mut data) = match self {
            Ix::Initialize(Init { tree, token, config, authority, system, signs }) => (
                "initialize",
                vec![w(*tree, false), w(*token, false), w(*config, false), w(*authority, *signs), r(*system, false)],
                vec![],
            ),
            Ix::UpdateDepositLimit { tree, authority, signs, new_limit } => (
                "update_deposit_limit",
                vec![w(*tree, false), r(*authority, *signs)],
                new_limit.to_le_bytes().to_vec(),
            ),
            Ix::UpdateGlobalConfig { config, authority, signs, dep, wd, margin } => {
                let mut d = Vec::new();
                borsh_option_u16(&mut d, *dep);
                borsh_option_u16(&mut d, *wd);
                borsh_option_u16(&mut d, *margin);
                ("update_global_config", vec![w(*config, false), r(*authority, *signs)], d)
            }
            Ix::Transact(t) => {
                let p = &t.proof;
                let mut d = Vec::new();
                for part in [&p.proof_a[..], &p.proof_b[..], &p.proof_c[..], &p.root[..], &p.public_amount[..], &p.ext_data_hash[..]] {
                    d.extend_from_slice(part);
                }
                p.input_nullifiers.iter().for_each(|n| d.extend_from_slice(n));
                p.output_commitments.iter().for_each(|c| d.extend_from_slice(c));
                d.extend_from_slice(&t.ext_amount.to_le_bytes());
                d.extend_from_slice(&t.fee.to_le_bytes());
                for out in [&t.out1, &t.out2] {
                    d.extend_from_slice(&(out.len() as u32).to_le_bytes());
                    d.extend_from_slice(out);
                }
                // Writable and signer flags as in the IDL.
                let accounts = vec![
                    w(t.tree, false), w(t.n0, false), w(t.n1, false), r(t.n2, false), r(t.n3, false),
                    w(t.token, false), r(t.config, false), w(t.recipient, false), w(t.fee_recipient, false),
                    w(t.signer, t.signs), r(t.system, false),
                ];
                ("transact", accounts, d)
            }
        };
        let mut bytes = discriminator("global", name).to_vec();
        bytes.append(&mut data);
        Instruction { program_id: program_id(), accounts, data: bytes }
    }

    fn signer(&self) -> Option<Pubkey> {
        match self {
            Ix::Initialize(Init { authority, signs, .. })
            | Ix::UpdateDepositLimit { authority, signs, .. }
            | Ix::UpdateGlobalConfig { authority, signs, .. } => signs.then_some(*authority),
            Ix::Transact(t) => t.signs.then_some(t.signer),
        }
    }

    fn lean(&self, keys: &Keys) -> String {
        let k = |p: &Pubkey| keys.name(p);
        match self {
            Ix::Initialize(Init { tree, token, config, authority, system, .. }) => format!(
                ".initialize {{ treeAccount := {}, treeTokenAccount := {}, globalConfig := {}, authority := {}, systemProgram := {} }}",
                k(tree), k(token), k(config), k(authority), k(system)
            ),
            Ix::UpdateDepositLimit { tree, authority, new_limit, .. } => format!(
                ".updateDepositLimit {{ treeAccount := {}, authority := {} }} (u64 {})",
                k(tree), k(authority), new_limit
            ),
            Ix::UpdateGlobalConfig { config, authority, dep, wd, margin, .. } => format!(
                ".updateGlobalConfig {{ globalConfig := {}, authority := {} }} (ou16 {}) (ou16 {}) (ou16 {})",
                k(config), k(authority), lean_opt_u16(*dep), lean_opt_u16(*wd), lean_opt_u16(*margin)
            ),
            Ix::Transact(t) => {
                let p = &t.proof;
                format!(
                    ".transact {{ treeAccount := {}, nullifier0 := {}, nullifier1 := {}, nullifier2 := {}, nullifier3 := {}, treeTokenAccount := {}, globalConfig := {}, recipient := {}, feeRecipientAccount := {}, signer := {}, systemProgram := {} }}\n      (proofOf {} {} {} {} {} {} {} {} {} {})\n      (i64 ({})) (u64 {}) (slice {}) (slice {})",
                    k(&t.tree), k(&t.n0), k(&t.n1), k(&t.n2), k(&t.n3), k(&t.token), k(&t.config),
                    k(&t.recipient), k(&t.fee_recipient), k(&t.signer), k(&t.system),
                    lean_hex(&p.proof_a), lean_hex(&p.proof_b), lean_hex(&p.proof_c), lean_hex(&p.root),
                    lean_hex(&p.public_amount), lean_hex(&p.ext_data_hash),
                    lean_hex(&p.input_nullifiers[0]), lean_hex(&p.input_nullifiers[1]),
                    lean_hex(&p.output_commitments[0]), lean_hex(&p.output_commitments[1]),
                    t.ext_amount, t.fee, lean_hex(&t.out1), lean_hex(&t.out2)
                )
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Running

struct World {
    svm: LiteSVM,
    payer: Keypair,
}

impl World {
    fn new(so: &[u8]) -> World {
        let mut svm = LiteSVM::new().with_sigverify(false).with_transaction_history(0);
        svm.add_program(program_id(), so);
        let payer = Keypair::new();
        svm.airdrop(&payer.pubkey(), 100 * SOL).unwrap();
        World { svm, payer }
    }

    fn fund(&mut self, key: &Pubkey, lamports: u64) {
        self.svm
            .set_account(*key, Account { lamports, data: vec![], owner: SYSTEM_PROGRAM, executable: false, rent_epoch: 0 })
            .unwrap();
    }

    /// Sends `ix`; the fee payer signs, the other signatures are left empty
    /// (signature verification is off, so the authority need not be ours).
    fn send(&mut self, ix: &Ix) -> Result<litesvm::types::TransactionMetadata, litesvm::types::FailedTransactionMetadata> {
        // A compute budget instruction first (`transact` needs more than the
        // default), so the program's instruction is instruction 1.
        let budget = Instruction {
            program_id: Pubkey::from_str("ComputeBudget111111111111111111111111111111").unwrap(),
            accounts: vec![],
            data: [&[2u8][..], &1_400_000u32.to_le_bytes()[..]].concat(),
        };
        let msg = Message::new(&[budget, ix.instruction()], Some(&self.payer.pubkey()));
        let mut tx = Transaction::new_unsigned(msg);
        tx.partial_sign(&[&self.payer], self.svm.latest_blockhash());
        self.svm.send_transaction(tx)
    }
}

/// How an instruction failed, as far as the model distinguishes it.
fn classify(f: &litesvm::types::FailedTransactionMetadata) -> String {
    use solana_instruction::error::InstructionError;
    let logs = f.meta.logs.join("\n");
    match &f.err {
        TransactionError::InstructionError(1, InstructionError::Custom(c)) => {
            if logs.contains("AnchorError caused by account:") {
                format!(".accounts {:?}", anchor_error_line(&logs))
            } else if (6000..6100).contains(c) {
                format!(".program {c}")
            } else if *c >= 100 {
                format!(".anchor {c} {:?}", anchor_error_line(&logs))
            } else {
                format!(".system {c}")
            }
        }
        TransactionError::InstructionError(1, e) => format!(".runtime {:?}", format!("{e:?}")),
        e => panic!("transaction-level error (a harness bug): {e:?}"),
    }
}

fn anchor_error_line(logs: &str) -> String {
    logs.lines().find(|l| l.contains("AnchorError")).unwrap_or("").trim().to_string()
}

/// The events in the logs (`Program data:` lines), as `(index, commitment, output)`.
fn events(logs: &[String]) -> Vec<(u64, [u8; 32], Vec<u8>)> {
    let disc = discriminator("event", "CommitmentData");
    logs.iter()
        .filter_map(|l| l.strip_prefix("Program data: "))
        .map(|b64| {
            let b = base64::engine::general_purpose::STANDARD.decode(b64).unwrap();
            assert_eq!(&b[..8], &disc, "unknown event");
            let len = u32::from_le_bytes(arr(&b, 48)) as usize;
            assert_eq!(b.len(), 52 + len, "event does not decode exactly");
            (u64_at(&b, 8), arr(&b, 16), b[52..].to_vec())
        })
        .collect()
}

/// One scenario: a name, the setup (instructions or account writes run first),
/// and the instruction whose step is traced.
struct Scenario {
    name: String,
    setup: Box<dyn Fn(&mut World, &Addrs)>,
    ix: Box<dyn Fn(&Addrs) -> Ix>,
}

/// The addresses scenarios use.
struct Addrs {
    admin: Pubkey,
    other: Pubkey,
    tree: Pubkey,
    token: Pubkey,
    config: Pubkey,
    stranger: Pubkey,
    /// An address (no key) where copies of program accounts are placed.
    other_account: Pubkey,
    /// The recipient and fee recipient the proofs' ext data name, and the
    /// user who signs `transact`.
    recipient: Pubkey,
    fee_recipient: Pubkey,
    user: Pubkey,
    /// The proofs of proofs/proofs.json, by name.
    proofs: std::collections::HashMap<String, Fixture>,
}

/// One proof of proofs/proofs.json, with the ext data it was made for.
#[derive(Clone, serde::Deserialize)]
struct Fixture {
    proof_a: Vec<u8>,
    proof_b: Vec<u8>,
    proof_c: Vec<u8>,
    root: Vec<u8>,
    public_amount: Vec<u8>,
    ext_data_hash: Vec<u8>,
    input_nullifiers: Vec<Vec<u8>>,
    output_commitments: Vec<Vec<u8>>,
    ext_amount: String,
    fee: String,
    encrypted_output1: String,
    encrypted_output2: String,
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

impl Fixture {
    fn proof(&self) -> zkcash_core::transact::Proof {
        let a32 = |v: &[u8]| -> [u8; 32] { v.try_into().unwrap() };
        zkcash_core::transact::Proof {
            proof_a: self.proof_a.as_slice().try_into().unwrap(),
            proof_b: self.proof_b.as_slice().try_into().unwrap(),
            proof_c: self.proof_c.as_slice().try_into().unwrap(),
            root: a32(&self.root),
            public_amount: a32(&self.public_amount),
            ext_data_hash: a32(&self.ext_data_hash),
            input_nullifiers: [a32(&self.input_nullifiers[0]), a32(&self.input_nullifiers[1])],
            output_commitments: [a32(&self.output_commitments[0]), a32(&self.output_commitments[1])],
        }
    }
}

/// `transact` with the proof `name`, its ext data, and the canonical accounts.
fn tx(a: &Addrs, name: &str) -> Tx {
    let f = &a.proofs[name];
    let proof = f.proof();
    let [n0, n1] = proof.input_nullifiers;
    Tx {
        tree: a.tree,
        n0: pda(&[b"nullifier0", &n0]).0,
        n1: pda(&[b"nullifier1", &n1]).0,
        n2: pda(&[b"nullifier0", &n1]).0,
        n3: pda(&[b"nullifier1", &n0]).0,
        token: a.token,
        config: a.config,
        recipient: a.recipient,
        fee_recipient: a.fee_recipient,
        signer: a.user,
        system: SYSTEM_PROGRAM,
        signs: true,
        proof,
        ext_amount: f.ext_amount.parse().unwrap(),
        fee: f.fee.parse().unwrap(),
        out1: unhex(&f.encrypted_output1),
        out2: unhex(&f.encrypted_output2),
    }
}

fn tx_ix(a: &Addrs, name: &str) -> Ix {
    Ix::Transact(Box::new(tx(a, name)))
}

fn deposited(w: &mut World, a: &Addrs) {
    initialized(w, a);
    w.fund(&a.user, 10 * SOL);
    w.send(&tx_ix(a, "deposit")).expect("setup deposit failed");
}

fn withdrawn(w: &mut World, a: &Addrs) {
    deposited(w, a);
    w.send(&tx_ix(a, "withdraw")).expect("setup withdrawal failed");
}

fn pda(seeds: &[&[u8]]) -> (Pubkey, u8) {
    Pubkey::find_program_address(seeds, &program_id())
}

fn init(a: &Addrs, authority: Pubkey) -> Init {
    Init { tree: a.tree, token: a.token, config: a.config, authority, system: SYSTEM_PROGRAM, signs: true }
}

fn init_ix(a: &Addrs, authority: Pubkey) -> Ix {
    Ix::Initialize(init(a, authority))
}

fn initialized(w: &mut World, a: &Addrs) {
    w.fund(&a.admin, 10 * SOL);
    w.send(&init_ix(a, a.admin)).expect("setup initialize failed");
}

fn s(name: impl Into<String>, setup: impl Fn(&mut World, &Addrs) + 'static, ix: impl Fn(&Addrs) -> Ix + 'static) -> Scenario {
    Scenario { name: name.into(), setup: Box::new(setup), ix: Box::new(ix) }
}

/// The `space` of each account type (`8 + size_of::<T>()`).
fn space(d: &Data) -> usize {
    match d {
        Data::Tree(_) => 4136,
        Data::TreeToken { .. } => 41,
        Data::GlobalConfig { .. } => 48,
        Data::Nullifier { .. } => 9,
        Data::Empty | Data::Foreign => 0,
    }
}

/// Writes an account directly (states the scenarios start from).
fn put(w: &mut World, key: Pubkey, owner: Pubkey, data: &Data, lamports: u64) {
    let bytes = if matches!(data, Data::Empty) { vec![] } else { encode(data, space(data)) };
    w.svm.set_account(key, Account { lamports, data: bytes, owner, executable: false, rent_epoch: 0 }).unwrap();
}

/// An account's lamports and decoded data.
fn read(w: &World, key: &Pubkey) -> (u64, Data) {
    let a = w.svm.get_account(key).expect("account exists");
    (a.lamports, decode(&a.owner, &a.data))
}

/// Rewrites the stored bump of the tree or config at `key`.
fn set_bump(w: &mut World, key: Pubkey, bump: u8) {
    let (lamports, mut d) = read(w, &key);
    match &mut d {
        Data::Tree(t) => t.bump = bump,
        Data::GlobalConfig { bump: b, .. } => *b = bump,
        _ => panic!("no bump to set"),
    }
    put(w, key, program_id(), &d, lamports);
}

/// Copies the account at `from` to `to`, owned by `owner`.
fn copy_to(w: &mut World, from: Pubkey, to: Pubkey, owner: Pubkey) {
    let (lamports, d) = read(w, &from);
    put(w, to, owner, &d, lamports);
}

fn scenarios() -> Vec<Scenario> {
    let mut v = fixed_scenarios();
    v.extend(random_scenarios(150));
    v.extend(transact_scenarios());
    v
}

fn with(a: &Addrs, name: &str, f: impl FnOnce(&mut Tx)) -> Ix {
    let mut t = tx(a, name);
    f(&mut t);
    Ix::Transact(Box::new(t))
}

fn funded_initialized(w: &mut World, a: &Addrs) {
    initialized(w, a);
    w.fund(&a.user, 10 * SOL);
}

fn transact_scenarios() -> Vec<Scenario> {
    vec![
        // the protocol's paths
        s("transact: deposit", funded_initialized, |a| tx_ix(a, "deposit")),
        s("transact: withdrawal", deposited, |a| tx_ix(a, "withdraw")),
        // double spends
        s("transact: the deposit replayed (its nullifiers are spent)", deposited, |a| tx_ix(a, "deposit")),
        s("transact: the withdrawal replayed (note spent in slot 0)", withdrawn, |a| tx_ix(a, "withdraw")),
        s("transact: the note spent in slot 0, then in slot 1", withdrawn, |a| tx_ix(a, "withdraw_slot1")),
        // the handler's checks
        s("transact: withdrawal before the deposit (unknown root)", funded_initialized, |a| tx_ix(a, "withdraw")),
        s("transact: ext amount not the proof's", funded_initialized, |a| with(a, "deposit", |t| t.ext_amount += 1)),
        s("transact: recipient not the proof's", funded_initialized, |a| with(a, "deposit", |t| t.recipient = a.other)),
        s("transact: corrupted proof", funded_initialized, |a| with(a, "deposit", |t| t.proof.proof_c[5] ^= 1)),
        s("transact: output commitment not the proof's", funded_initialized, |a| {
            with(a, "deposit", |t| t.proof.output_commitments[1][31] ^= 1)
        }),
        s(
            "transact: deposit above the limit",
            |w, a| {
                funded_initialized(w, a);
                w.send(&Ix::UpdateDepositLimit { tree: a.tree, authority: a.admin, signs: true, new_limit: 999_999 })
                    .expect("setup limit");
            },
            |a| tx_ix(a, "deposit"),
        ),
        s(
            "transact: signer cannot pay the deposit",
            |w, a| {
                initialized(w, a);
                let rent = w.svm.minimum_balance_for_rent_exemption(9);
                w.fund(&a.user, 2 * rent + 500_000);
            },
            |a| tx_ix(a, "deposit"),
        ),
        s(
            "transact: pool cannot pay the withdrawal",
            |w, a| {
                deposited(w, a);
                let mut acc = w.svm.get_account(&a.token).unwrap();
                acc.lamports = w.svm.minimum_balance_for_rent_exemption(41);
                w.svm.set_account(a.token, acc).unwrap();
            },
            |a| tx_ix(a, "withdraw"),
        ),
        // the accounts
        s("transact: before initialize", |w, a| w.fund(&a.user, 10 * SOL), |a| tx_ix(a, "deposit")),
        s("transact: signer did not sign", funded_initialized, |a| with(a, "deposit", |t| t.signs = false)),
        s("transact: nullifier0 not its PDA", funded_initialized, |a| with(a, "deposit", |t| t.n0 = a.stranger)),
        s("transact: cross-check nullifiers swapped", funded_initialized, |a| {
            with(a, "deposit", |t| std::mem::swap(&mut t.n2, &mut t.n3))
        }),
        s("transact: config passed as the tree", funded_initialized, |a| with(a, "deposit", |t| t.tree = a.config)),
        s("transact: tree passed as the pool", funded_initialized, |a| with(a, "deposit", |t| t.token = a.tree)),
    ]
}

fn fixed_scenarios() -> Vec<Scenario> {
    vec![
        // initialize
        s("initialize by the admin", |w, a| w.fund(&a.admin, 10 * SOL), |a| init_ix(a, a.admin)),
        s("initialize by someone else", |w, a| w.fund(&a.other, 10 * SOL), |a| init_ix(a, a.other)),
        s("initialize twice", initialized, |a| init_ix(a, a.admin)),
        s("initialize, admin did not sign", |w, a| w.fund(&a.admin, 10 * SOL), |a| Ix::Initialize(Init { signs: false, ..init(a, a.admin) })),
        s("initialize, tree not its PDA", |w, a| w.fund(&a.admin, 10 * SOL), |a| Ix::Initialize(Init { tree: a.stranger, ..init(a, a.admin) })),
        s("initialize, config not its PDA", |w, a| w.fund(&a.admin, 10 * SOL), |a| Ix::Initialize(Init { config: a.stranger, ..init(a, a.admin) })),
        s("initialize, wrong system program", |w, a| w.fund(&a.admin, 10 * SOL), |a| Ix::Initialize(Init { system: a.stranger, ..init(a, a.admin) })),
        s("initialize, admin cannot pay the rent", |w, a| w.fund(&a.admin, 1_000_000), |a| init_ix(a, a.admin)),
        s(
            "initialize, tree already holds lamports (top-up)",
            |w, a| {
                w.fund(&a.admin, 10 * SOL);
                w.fund(&a.tree, 1_000_000);
            },
            |a| init_ix(a, a.admin),
        ),
        s(
            "initialize, tree already above rent (no transfer)",
            |w, a| {
                w.fund(&a.admin, 10 * SOL);
                w.fund(&a.tree, 50_000_000);
            },
            |a| init_ix(a, a.admin),
        ),
        // update_deposit_limit
        s("update_deposit_limit by the authority", initialized, |a| {
            Ix::UpdateDepositLimit { tree: a.tree, authority: a.admin, signs: true, new_limit: 5 * SOL }
        }),
        s("update_deposit_limit by someone else", initialized, |a| {
            Ix::UpdateDepositLimit { tree: a.tree, authority: a.other, signs: true, new_limit: 5 * SOL }
        }),
        s("update_deposit_limit, authority did not sign", initialized, |a| {
            Ix::UpdateDepositLimit { tree: a.tree, authority: a.admin, signs: false, new_limit: 5 * SOL }
        }),
        s("update_deposit_limit, config passed as the tree", initialized, |a| {
            Ix::UpdateDepositLimit { tree: a.config, authority: a.admin, signs: true, new_limit: 5 * SOL }
        }),
        s("update_deposit_limit before initialize", |w, a| w.fund(&a.admin, SOL), |a| {
            Ix::UpdateDepositLimit { tree: a.tree, authority: a.admin, signs: true, new_limit: 5 * SOL }
        }),
        // update_global_config
        s("update_global_config by the authority", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: Some(10), wd: None, margin: Some(100) }
        }),
        s("update_global_config, nothing to change", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: None, wd: None, margin: None }
        }),
        s("update_global_config, rates at the 10000 limit", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: Some(10000), wd: Some(10000), margin: Some(10000) }
        }),
        s("update_global_config, deposit rate above 10000", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: Some(10001), wd: None, margin: None }
        }),
        s("update_global_config, margin above 10000", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: None, wd: None, margin: Some(10001) }
        }),
        s("update_global_config by someone else", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.other, signs: true, dep: Some(10), wd: None, margin: None }
        }),
        s("update_global_config, tree passed as the config", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.tree, authority: a.admin, signs: true, dep: Some(10), wd: None, margin: None }
        }),
        // update_global_config: each account check, and the boundaries
        s("update_global_config, authority did not sign", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: false, dep: Some(10), wd: None, margin: None }
        }),
        s(
            "update_global_config, a copy of the config at another address",
            |w, a| {
                initialized(w, a);
                copy_to(w, a.config, a.stranger, program_id());
            },
            |a| Ix::UpdateGlobalConfig { config: a.stranger, authority: a.admin, signs: true, dep: Some(10), wd: None, margin: None },
        ),
        s(
            "update_global_config, config with a wrong stored bump",
            |w, a| {
                initialized(w, a);
                set_bump(w, a.config, 7);
            },
            |a| Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: Some(10), wd: None, margin: None },
        ),
        s(
            "update_global_config, config owned by another program",
            |w, a| {
                initialized(w, a);
                copy_to(w, a.config, a.config, a.stranger);
            },
            |a| Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: Some(10), wd: None, margin: None },
        ),
        s("update_global_config, all rates zero", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: Some(0), wd: Some(0), margin: Some(0) }
        }),
        s("update_global_config, withdrawal rate above 10000", initialized, |a| {
            Ix::UpdateGlobalConfig { config: a.config, authority: a.admin, signs: true, dep: None, wd: Some(u16::MAX), margin: None }
        }),
        // update_deposit_limit: each account check, and the boundaries
        s(
            "update_deposit_limit, a copy of the tree at another address",
            |w, a| {
                initialized(w, a);
                copy_to(w, a.tree, a.stranger, program_id());
            },
            |a| Ix::UpdateDepositLimit { tree: a.stranger, authority: a.admin, signs: true, new_limit: 5 * SOL },
        ),
        s(
            "update_deposit_limit, tree with a wrong stored bump",
            |w, a| {
                initialized(w, a);
                set_bump(w, a.tree, 7);
            },
            |a| Ix::UpdateDepositLimit { tree: a.tree, authority: a.admin, signs: true, new_limit: 5 * SOL },
        ),
        s(
            "update_deposit_limit, tree owned by another program",
            |w, a| {
                initialized(w, a);
                copy_to(w, a.tree, a.tree, a.stranger);
            },
            |a| Ix::UpdateDepositLimit { tree: a.tree, authority: a.admin, signs: true, new_limit: 5 * SOL },
        ),
        s("update_deposit_limit to 0", initialized, |a| {
            Ix::UpdateDepositLimit { tree: a.tree, authority: a.admin, signs: true, new_limit: 0 }
        }),
        s("update_deposit_limit to u64::MAX", initialized, |a| {
            Ix::UpdateDepositLimit { tree: a.tree, authority: a.admin, signs: true, new_limit: u64::MAX }
        }),
        s("update_deposit_limit, the pool passed as the tree", initialized, |a| {
            Ix::UpdateDepositLimit { tree: a.token, authority: a.admin, signs: true, new_limit: 5 * SOL }
        }),
        // initialize: partial state, funding paths, duplicates
        s(
            "initialize, the config already exists",
            |w, a| {
                initialized(w, a);
                put(w, a.tree, SYSTEM_PROGRAM, &Data::Empty, 0);
                put(w, a.token, SYSTEM_PROGRAM, &Data::Empty, 0);
            },
            |a| init_ix(a, a.admin),
        ),
        s(
            "initialize, pool and config already hold lamports",
            |w, a| {
                w.fund(&a.admin, 10 * SOL);
                w.fund(&a.token, 500_000);
                w.fund(&a.config, 2_000_000);
            },
            |a| init_ix(a, a.admin),
        ),
        s(
            "initialize, admin can pay the tree but not the rest",
            |w, a| w.fund(&a.admin, w.svm.minimum_balance_for_rent_exemption(4136) + 1),
            |a| init_ix(a, a.admin),
        ),
        s("initialize, tree passed as the pool", |w, a| w.fund(&a.admin, 10 * SOL), |a| {
            Ix::Initialize(Init { token: a.tree, ..init(a, a.admin) })
        }),
        s("initialize, the admin passed as the system program", |w, a| w.fund(&a.admin, 10 * SOL), |a| {
            Ix::Initialize(Init { system: a.admin, ..init(a, a.admin) })
        }),
        s(
            "initialize, tree address holds data of another program",
            |w, a| {
                w.fund(&a.admin, 10 * SOL);
                w.svm
                    .set_account(a.tree, Account { lamports: 1_000_000, data: vec![1, 2, 3], owner: a.stranger, executable: false, rent_epoch: 0 })
                    .unwrap();
            },
            |a| init_ix(a, a.admin),
        ),
    ]
}

/// Deterministic xorshift, so the random scenarios are the same on every run.
struct Xorshift(u64);

impl Xorshift {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
    fn chance(&mut self, percent: u64) -> bool {
        self.below(100) < percent
    }
}

/// The choices a random scenario makes.
#[derive(Clone, Copy, Debug)]
struct RandomCase {
    kind: u64,
    initialized: bool,
    authority_funds: u64,
    prefund: [u64; 3],
    tamper_tree_bump: Option<u8>,
    tamper_config_bump: Option<u8>,
    tree_owned_by_stranger: bool,
    config_owned_by_stranger: bool,
    copy_tree_to_other: bool,
    copy_config_to_other: bool,
    slots: [u64; 3],
    authority: u64,
    signs: bool,
    system_ok: bool,
    new_limit: u64,
    rates: [Option<u16>; 3],
}

fn random_option_u16(r: &mut Xorshift) -> Option<u16> {
    match r.below(7) {
        0 | 1 => None,
        2 => Some(0),
        3 => Some(10000),
        4 => Some(10001),
        5 => Some(u16::MAX),
        _ => Some(r.below(20000) as u16),
    }
}

fn random_case(r: &mut Xorshift) -> RandomCase {
    let rent_total = 29_677_440 + 1_176_240 + 1_224_960;
    RandomCase {
        kind: r.below(3),
        initialized: r.chance(70),
        authority_funds: match r.below(4) {
            0 => r.below(rent_total),
            _ => 10 * SOL,
        },
        prefund: [0; 3].map(|_| if r.chance(15) { r.below(40_000_000) + 1 } else { 0 }),
        tamper_tree_bump: r.chance(10).then(|| r.below(256) as u8),
        tamper_config_bump: r.chance(10).then(|| r.below(256) as u8),
        tree_owned_by_stranger: r.chance(5),
        config_owned_by_stranger: r.chance(5),
        copy_tree_to_other: r.chance(10),
        copy_config_to_other: r.chance(10),
        // which address goes in each account slot: mostly the right one
        slots: [0; 3].map(|_| if r.chance(75) { 0 } else { r.below(5) }),
        authority: if r.chance(70) { 0 } else { r.below(3) },
        signs: r.chance(85),
        system_ok: r.chance(90),
        new_limit: match r.below(5) {
            0 => 0,
            1 => u64::MAX,
            _ => r.next(),
        },
        rates: [0; 3].map(|_| random_option_u16(r)),
    }
}

impl RandomCase {
    fn setup(&self, w: &mut World, a: &Addrs) {
        let authority = self.authority_key(a);
        if self.initialized {
            initialized(w, a);
            if let Some(b) = self.tamper_tree_bump {
                set_bump(w, a.tree, b);
            }
            if let Some(b) = self.tamper_config_bump {
                set_bump(w, a.config, b);
            }
            if self.copy_tree_to_other {
                copy_to(w, a.tree, a.other_account, program_id());
            }
            if self.copy_config_to_other {
                copy_to(w, a.config, a.other_account, program_id());
            }
            if self.tree_owned_by_stranger {
                copy_to(w, a.tree, a.tree, a.stranger);
            }
            if self.config_owned_by_stranger {
                copy_to(w, a.config, a.config, a.stranger);
            }
        } else {
            for (key, lamports) in [a.tree, a.token, a.config].iter().zip(self.prefund) {
                if lamports > 0 {
                    w.fund(key, lamports);
                }
            }
        }
        // The authority's lamports (on top of what setup left it).
        let (have, _) = w.svm.get_account(&authority).map(|x| (x.lamports, ())).unwrap_or((0, ()));
        w.fund(&authority, have.max(self.authority_funds));
    }

    fn authority_key(&self, a: &Addrs) -> Pubkey {
        [a.admin, a.other, a.stranger][self.authority as usize]
    }

    /// The address put in an account slot whose right address is `right`.
    fn slot(&self, i: usize, right: Pubkey, a: &Addrs) -> Pubkey {
        [right, a.tree, a.token, a.config, a.other_account][self.slots[i] as usize]
    }

    fn ix(&self, a: &Addrs) -> Ix {
        let authority = self.authority_key(a);
        match self.kind {
            0 => Ix::Initialize(Init {
                tree: self.slot(0, a.tree, a),
                token: self.slot(1, a.token, a),
                config: self.slot(2, a.config, a),
                authority,
                system: if self.system_ok { SYSTEM_PROGRAM } else { a.stranger },
                signs: self.signs,
            }),
            1 => Ix::UpdateDepositLimit { tree: self.slot(0, a.tree, a), authority, signs: self.signs, new_limit: self.new_limit },
            _ => Ix::UpdateGlobalConfig {
                config: self.slot(2, a.config, a),
                authority,
                signs: self.signs,
                dep: self.rates[0],
                wd: self.rates[1],
                margin: self.rates[2],
            },
        }
    }
}

fn random_scenarios(n: usize) -> Vec<Scenario> {
    let mut r = Xorshift(0x5eed_0f_c0_f0_12_3456);
    (0..n)
        .map(|i| {
            let c = random_case(&mut r);
            let name = format!("random {i}: {c:?}");
            s(name, move |w, a| c.setup(w, a), move |a| c.ix(a))
        })
        .collect()
}

/// The crypto answers of a `transact` scenario (see `replay`), as Lean; none
/// if its tree or config is not one (it then fails before any crypto).
fn crypto_tables(pre: &BTreeMap<usize, Option<Account>>, ks: &[Pubkey], t: &Tx) -> String {
    let data = |k: &Pubkey| ks.iter().position(|x| x == k).and_then(|i| pre[&i].clone()).map(|a| decode(&a.owner, &a.data));
    let (Some(Data::Tree(tr)), Some(Data::GlobalConfig { authority, deposit, withdrawal, margin, bump })) = (data(&t.tree), data(&t.config))
    else {
        return "{}".to_string();
    };
    let tree = zkcash_core::merkle_tree::MerkleTreeAccount {
        authority: tr.authority,
        next_index: tr.next_index,
        subtrees: tr.subtrees.clone().try_into().unwrap(),
        root: tr.root,
        root_history: tr.root_history.clone().try_into().unwrap(),
        root_index: tr.root_index,
        max_deposit_amount: tr.max_deposit_amount,
        height: tr.height,
        root_history_size: tr.root_history_size,
        bump: tr.bump,
        _padding: tr.padding,
    };
    let config = zkcash_core::admin::GlobalConfig {
        authority,
        deposit_fee_rate: deposit,
        withdrawal_fee_rate: withdrawal,
        fee_error_margin: margin,
        bump,
    };
    let tb = replay::tables(
        tree, config, &t.proof, t.ext_amount, t.fee, t.recipient.to_bytes(), t.fee_recipient.to_bytes(), &t.out1, &t.out2,
    );
    let opt = |o: Option<String>| o.map_or("none".into(), |x| format!("(some {x})"));
    let list = |v: Vec<String>| format!("[{}]", v.join(",\n          "));
    format!(
        "\n      {{ poseidon := {},\n        sha := {},\n        multiplication := {},\n        addition := {},\n        pairing := {} }}",
        list(tb.poseidon.iter().map(|(l, r, o)| format!("({}, {}, {})", lean_hex(l), lean_hex(r), lean_hex(o))).collect()),
        list(tb.sha256.iter().map(|(i, o)| format!("({}, {})", lean_hex(i), lean_hex(o))).collect()),
        list(tb.multiplication.iter().map(|(i, o)| format!("({}, {})", lean_hex(i), opt(o.map(|x| lean_hex(&x))))).collect()),
        list(tb.addition.iter().map(|(i, o)| format!("({}, {})", lean_hex(i), opt(o.map(|x| lean_hex(&x))))).collect()),
        list(tb.pairing.iter().map(|(i, o)| format!("({}, {})", lean_hex(i), opt(o.map(|x| lean_hex(&x))))).collect()),
    )
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 4, "usage: conformance <zkcash.so> <idl.json> <proofs.json>");
    let so = std::fs::read(&args[1]).expect("read zkcash.so");
    let idl: serde_json::Value = serde_json::from_str(&std::fs::read_to_string(&args[2]).expect("read IDL")).unwrap();

    // The encoders' discriminators are the IDL's.
    for ix in idl["instructions"].as_array().unwrap() {
        let name = ix["name"].as_str().unwrap();
        let d: Vec<u8> = ix["discriminator"].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as u8).collect();
        assert_eq!(d, discriminator("global", name), "instruction discriminator of {name}");
    }
    for (kind, ns) in [("accounts", "account"), ("events", "event")] {
        for a in idl[kind].as_array().unwrap() {
            let name = a["name"].as_str().unwrap();
            let d: Vec<u8> = a["discriminator"].as_array().unwrap().iter().map(|x| x.as_u64().unwrap() as u8).collect();
            assert_eq!(d, discriminator(ns, name), "{ns} discriminator of {name}");
        }
    }

    let (tree, tree_bump) = pda(&[b"merkle_tree"]);
    let (token, token_bump) = pda(&[b"tree_token"]);
    let (config, config_bump) = pda(&[b"global_config"]);
    let addrs = Addrs {
        admin: Pubkey::from_str(ADMIN).unwrap(),
        other: Pubkey::new_from_array([0x0a; 32]),
        tree,
        token,
        config,
        stranger: Pubkey::new_from_array([0x0b; 32]),
        other_account: Pubkey::new_from_array([0x0c; 32]),
        recipient: Pubkey::new_from_array([0x0d; 32]),
        fee_recipient: Pubkey::new_from_array([0x0e; 32]),
        user: Pubkey::new_from_array([0x0f; 32]),
        proofs: serde_json::from_str(&std::fs::read_to_string(&args[3]).expect("read proofs.json")).unwrap(),
    };
    let probe = World::new(&so);
    let native_loader = probe.svm.get_account(&SYSTEM_PROGRAM).unwrap().owner;
    // The empty tree's subtrees and root: `initialize` writes zero_bytes[0..26]
    // as the subtrees and zero_bytes[26] as the root.
    let (zero_subtrees, zero_root) = {
        let mut w = World::new(&so);
        initialized(&mut w, &addrs);
        let Data::Tree(t) = read(&w, &tree).1 else { panic!("no tree") };
        (t.subtrees.clone(), t.root)
    };
    let keys = Keys(vec![
        ("keyProgram".into(), program_id()),
        ("keyNativeLoader".into(), native_loader),
        ("keySystem".into(), SYSTEM_PROGRAM),
        ("keyAdmin".into(), addrs.admin),
        ("keyOther".into(), addrs.other),
        ("keyStranger".into(), addrs.stranger),
        ("keyOtherAccount".into(), addrs.other_account),
        ("keyRecipient".into(), addrs.recipient),
        ("keyFeeRecipient".into(), addrs.fee_recipient),
        ("keyUser".into(), addrs.user),
        ("keyTree".into(), tree),
        ("keyTreeToken".into(), token),
        ("keyGlobalConfig".into(), config),
    ], zero_subtrees.clone());

    println!("-- BEGIN GENERATED");
    for (n, k) in &keys.0 {
        println!("def {n} : Pubkey := pk {}", lean_hex(k.as_ref()));
    }
    println!();
    println!("/-- `find_program_address` on the seeds the scenarios use: (seeds, bump). -/");
    println!("def bumps : List (List Nat × Nat) := [");
    let mut seeds: Vec<(Vec<u8>, u8, Pubkey)> = vec![
        (b"merkle_tree".to_vec(), tree_bump, tree),
        (b"tree_token".to_vec(), token_bump, token),
        (b"global_config".to_vec(), config_bump, config),
    ];
    // Every nullifier of every proof, in both slots.
    let mut names: Vec<&String> = addrs.proofs.keys().collect();
    names.sort();
    for name in names {
        for n in &addrs.proofs[name].input_nullifiers {
            for slot in [&b"nullifier0"[..], &b"nullifier1"[..]] {
                let (p, b) = pda(&[slot, n]);
                let sd = [slot, &n[..]].concat();
                if !seeds.iter().any(|(s, _, _)| *s == sd) {
                    seeds.push((sd, b, p));
                }
            }
        }
    }
    let lines: Vec<String> = seeds.iter().map(|(s, b, _)| format!("  ({:?}, {b})", s)).collect();
    println!("{}\n]", lines.join(",\n"));
    println!();
    println!("/-- `create_program_address` on those seeds and bumps: (seeds ‖ bump, address). -/");
    println!("def addresses : List (List Nat × Pubkey) := [");
    let lines: Vec<String> = seeds
        .iter()
        .map(|(s, b, p)| {
            let mut v = s.clone();
            v.push(*b);
            format!("  ({v:?}, {})", keys.name(p))
        })
        .collect();
    println!("{}\n]", lines.join(",\n"));
    println!();
    println!("/-- `Rent::minimum_balance(space)` for the spaces the program creates. -/");
    println!("def rent : List (Nat × Nat) := [");
    let lines: Vec<String> = [4136usize, 41, 48, 9]
        .iter()
        .map(|n| format!("  ({n}, {})", probe.svm.minimum_balance_for_rent_exemption(*n)))
        .collect();
    println!("{}\n]", lines.join(",\n"));
    println!();
    println!("/-- The program's `zero_bytes` (Poseidon empty-subtree roots), as written by `initialize`. -/");
    {
        let zb = replay::zero_bytes();
        assert_eq!(&zb[..26], &zero_subtrees[..], "initialize did not write zero_bytes as the subtrees");
        assert_eq!(zb[26], zero_root, "initialize did not write zero_bytes[26] as the root");
        println!("def zeroBytesList : List String := {}", lean_hex_list(&zb));
        println!("def zeroSubtrees : List String := zeroBytesList.take 26");
    }
    println!();
    println!("def scenarios : List Scenario := [");
    let all = scenarios();
    for (i, sc) in all.iter().enumerate() {
        let mut w = World::new(&so);
        (sc.setup)(&mut w, &addrs);
        let ix = (sc.ix)(&addrs);
        let inst = ix.instruction();
        let mut ks: Vec<Pubkey> = Vec::new();
        for m in &inst.accounts {
            if !ks.contains(&m.pubkey) {
                ks.push(m.pubkey);
            }
        }
        assert!(!ks.contains(&w.payer.pubkey()), "the fee payer must not be an instruction account");
        let pre: BTreeMap<usize, Option<Account>> = ks.iter().enumerate().map(|(i, k)| (i, w.svm.get_account(k))).collect();
        let result = w.send(&ix);
        let outcome = match &result {
            Ok(meta) => {
                let post: Vec<String> = ks
                    .iter()
                    .map(|k| format!("({}, {})", keys.name(k), lean_account(&w.svm.get_account(k), &keys)))
                    .collect();
                let evs: Vec<String> = events(&meta.logs)
                    .iter()
                    .map(|(i, c, o)| format!("⟨u64 {i}, b32 {}, bytes {}⟩", lean_hex(c), lean_hex(o)))
                    .collect();
                format!(".ok [{}]\n      [{}]", post.join(",\n        "), evs.join(", "))
            }
            Err(f) => classify(f),
        };
        let crypto = match &ix {
            Ix::Transact(t) => crypto_tables(&pre, &ks, t),
            _ => "{}".to_string(),
        };
        let pre_s: Vec<String> =
            ks.iter().enumerate().map(|(i, k)| format!("({}, {})", keys.name(k), lean_account(&pre[&i], &keys))).collect();
        let signers: Vec<String> = ix.signer().iter().map(|k| keys.name(k)).collect();
        let sep = if i + 1 == all.len() { "" } else { "," };
        println!("  {{ title := {:?},", sc.name);
        println!("    pre := [{}],", pre_s.join(",\n      "));
        println!("    signers := [{}],", signers.join(", "));
        println!("    ix := {},", ix.lean(&keys));
        println!("    expected := {},", outcome);
        println!("    crypto := {} }}{sep}", crypto);
    }
    println!("]");
    println!("-- END GENERATED");
}
