//! Conformance traces: runs the compiled zkcash program (the mainnet build) in
//! LiteSVM on fixed scenarios and prints, as Lean, what happened: the accounts
//! of each instruction before and after, the events it emitted, or how it
//! failed. `core-model/Tests/Conformance.lean` runs the Lean model's `step` on
//! the same inputs and checks it agrees (`scripts/check_conformance.sh`).
//!
//! The harness is a client of the program, independent of its Rust crates:
//! it encodes instructions itself (Anchor discriminator + Borsh) and decodes
//! accounts itself. Both are checked: the discriminators against the IDL, and
//! every decoded account by re-encoding it to exactly its bytes.
//!
//! Usage: conformance <zkcash.so> <idl.json>

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

/// Names for the keys a trace mentions (`keyName` in Lean).
struct Keys(Vec<(String, Pubkey)>);

impl Keys {
    fn name(&self, k: &Pubkey) -> String {
        match self.0.iter().find(|(_, p)| p == k) {
            Some((n, _)) => n.clone(),
            None => format!("(pk {})", lean_hex(k.as_ref())),
        }
    }
}

fn lean_data(d: &Data, keys: &Keys) -> String {
    match d {
        Data::Empty => ".empty".into(),
        Data::Foreign => ".foreign".into(),
        Data::Tree(t) => format!(
            "(.treeAccount (tree {} {} {} {} {} {} {} {} {} {} {}))",
            keys.name(&Pubkey::new_from_array(t.authority)),
            t.next_index,
            lean_hex_list(&t.subtrees),
            lean_hex(&t.root),
            lean_hex_list(&t.root_history),
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

/// The SOL admin instructions. `signs` is whether the authority signs.
#[derive(Clone)]
enum Ix {
    Initialize(Init),
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
        let msg = Message::new(&[ix.instruction()], Some(&self.payer.pubkey()));
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
        TransactionError::InstructionError(0, InstructionError::Custom(c)) => {
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
        TransactionError::InstructionError(0, e) => format!(".runtime {:?}", format!("{e:?}")),
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
    name: &'static str,
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

fn scenarios() -> Vec<Scenario> {
    fn s(name: &'static str, setup: impl Fn(&mut World, &Addrs) + 'static, ix: impl Fn(&Addrs) -> Ix + 'static) -> Scenario {
        Scenario { name, setup: Box::new(setup), ix: Box::new(ix) }
    }
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
    ]
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    assert_eq!(args.len(), 3, "usage: conformance <zkcash.so> <idl.json>");
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
    };
    let probe = World::new(&so);
    let native_loader = probe.svm.get_account(&SYSTEM_PROGRAM).unwrap().owner;
    let keys = Keys(vec![
        ("keyProgram".into(), program_id()),
        ("keyNativeLoader".into(), native_loader),
        ("keySystem".into(), SYSTEM_PROGRAM),
        ("keyAdmin".into(), addrs.admin),
        ("keyOther".into(), addrs.other),
        ("keyStranger".into(), addrs.stranger),
        ("keyTree".into(), tree),
        ("keyTreeToken".into(), token),
        ("keyGlobalConfig".into(), config),
    ]);

    println!("-- BEGIN GENERATED");
    for (n, k) in &keys.0 {
        println!("def {n} : Pubkey := pk {}", lean_hex(k.as_ref()));
    }
    println!();
    println!("/-- `find_program_address` on the seeds the scenarios use: (seeds, bump). -/");
    println!("def bumps : List (List Nat × Nat) := [");
    let seeds: [(&[u8], u8, Pubkey); 3] =
        [(b"merkle_tree", tree_bump, tree), (b"tree_token", token_bump, token), (b"global_config", config_bump, config)];
    let lines: Vec<String> = seeds.iter().map(|(s, b, _)| format!("  ({:?}, {b})", s.to_vec())).collect();
    println!("{}\n]", lines.join(",\n"));
    println!();
    println!("/-- `create_program_address` on those seeds and bumps: (seeds ‖ bump, address). -/");
    println!("def addresses : List (List Nat × Pubkey) := [");
    let lines: Vec<String> = seeds
        .iter()
        .map(|(s, b, p)| {
            let mut v = s.to_vec();
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
        let mut w = World::new(&so);
        initialized(&mut w, &addrs);
        let acc = w.svm.get_account(&tree).unwrap();
        let Data::Tree(t) = decode(&acc.owner, &acc.data) else { panic!("no tree") };
        // `initialize` writes zero_bytes[0..26] as the subtrees and zero_bytes[26] as the root.
        let mut zb = t.subtrees.clone();
        zb.push(t.root);
        println!("def zeroBytesPrefix : List String := {}", lean_hex_list(&zb));
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
        let pre_s: Vec<String> =
            ks.iter().enumerate().map(|(i, k)| format!("({}, {})", keys.name(k), lean_account(&pre[&i], &keys))).collect();
        let signers: Vec<String> = ix.signer().iter().map(|k| keys.name(k)).collect();
        let sep = if i + 1 == all.len() { "" } else { "," };
        println!("  {{ title := {:?},", sc.name);
        println!("    pre := [{}],", pre_s.join(",\n      "));
        println!("    signers := [{}],", signers.join(", "));
        println!("    ix := {},", ix.lean(&keys));
        println!("    expected := {} }}{sep}", outcome);
    }
    println!("]");
    println!("-- END GENERATED");
}
