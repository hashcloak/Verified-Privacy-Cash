import PrivacyCash
import Spec.Statements
import Mathlib.Data.FinEnum
open Aeneas Aeneas.Std

/-! # Mapping: code-model values to spec values

REVIEW SURFACE. How code values, states and executions map to the spec's. The connection
theorems (`ConnectionTheorems.lean`) mean what these definitions say, so each is short.

A map that loses information makes a theorem weaker. Every map below is injective on the
values that matter, except where its docstring says otherwise (field elements are read mod p).

Names say where they come from:
- `Spec.…`: the spec.
- `CodeModel.…`: core-model (aliases, below).
- dot notation on a deployment `d` or a state `s` (`d.treeAddress`, `s.lamports k`): reads a
  value out of the code model; defined here (see "Readers"), the result is still a code value.
- no prefix: defined here, mostly maps between code and spec values (`toWorld`, `fromPubkey`, …).
-/

/-! ## `CodeModel`: short names for the code model

Aliases for everything the review files use from core-model: its Solana and Anchor model
(`PrivacyCash.Model`) and the extracted program (`zkcash_core`). So code types read
`CodeModel.State` or `CodeModel.MerkleTreeAccount` next to the spec's `Spec.World`. They are
names only, not new definitions. -/
namespace CodeModel
export PrivacyCash.Model (AltBn128 AltBn128Contracts CommitmentData Crypto Deployment EnvStep Event
  Event.env Event.program Genesis Groth16Sound HoldsGlobalConfig HoldsTree HoldsTreeToken
  Initializable InitializeAccounts Instruction PdaCollision Pubkey Reachable Run State
  TransactAccounts TxContext TxEnv arkFr bn254ScalarModulus bytesAt globalConfigSeeds
  globalConfigSpace leBytes32 merkleTreeSeeds nullifier0Seeds nullifier1Seeds nullifierAccountSpace
  publicInputs step systemProgram treeAccountSpace treeTokenAccountSpace treeTokenSeeds zeroTree)
export zkcash_core.merkle_tree (MerkleTreeAccount)
export zkcash_core.admin (GlobalConfig)
export zkcash_core.transact (Proof SOL_ADDRESS)
export zkcash_core.utils (check_public_amount)
export zkcash_core.verifying_key (VERIFYING_KEY)
end CodeModel

/-! ## Readers: values read out of the code model

Defined here, not in core-model, but in core-model's namespaces so they read as dot notation
on a deployment `d` or a state `s`. -/
namespace PrivacyCash.Model

/-- `d.treeAddress`: the SOL tree's address, the program's PDA with seeds `[b"merkle_tree"]`. -/
def Deployment.treeAddress (d : CodeModel.Deployment) : CodeModel.Pubkey :=
  d.pda CodeModel.merkleTreeSeeds
/-- `d.poolAddress`: the pool's address, the program's PDA with seeds `[b"tree_token"]`. -/
def Deployment.poolAddress (d : CodeModel.Deployment) : CodeModel.Pubkey :=
  d.pda CodeModel.treeTokenSeeds
/-- `d.configAddress`: the config's address, the program's PDA with seeds
    `[b"global_config"]`. -/
def Deployment.configAddress (d : CodeModel.Deployment) : CodeModel.Pubkey :=
  d.pda CodeModel.globalConfigSeeds
/-- `d.nullifierAddress i n`: the address of the nullifier account for nullifier `n` spent as
    input `i`, the program's PDA with seeds `[b"nullifier0", n]` for input 0 and
    `[b"nullifier1", n]` for input 1. -/
def Deployment.nullifierAddress (d : CodeModel.Deployment) (i : Fin 2)
    (n : Std.Array U8 32#usize) : CodeModel.Pubkey :=
  d.pda (if i = 0 then CodeModel.nullifier0Seeds n else CodeModel.nullifier1Seeds n)

/-- `s.treeAccount k`: the tree account data stored at `k`; the all-zero tree if `k` holds no
    tree, which `WellFormed` rules out at the tree's address. -/
def State.treeAccount (s : CodeModel.State) (k : CodeModel.Pubkey) :
    CodeModel.MerkleTreeAccount :=
  match (s k).data with
  | .treeAccount t => t
  | _ => CodeModel.zeroTree

/-- `s.configAccount k`: the config account data stored at `k`; the all-zero config if `k`
    holds no config. -/
def State.configAccount (s : CodeModel.State) (k : CodeModel.Pubkey) :
    CodeModel.GlobalConfig :=
  match (s k).data with
  | .globalConfig c => c
  | _ => ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩

/-- `s.lamports k`: the lamport balance of the account at `k`, as a number. -/
def State.lamports (s : CodeModel.State) (k : CodeModel.Pubkey) : ℕ := (s k).lamports.val

/-- `d.IsNullifierAccount s k`: the account at `k` is owned by the program and holds
    nullifier data. -/
def Deployment.IsNullifierAccount (d : CodeModel.Deployment) (s : CodeModel.State)
    (k : CodeModel.Pubkey) : Prop :=
  (s k).owner = d.programId ∧ ∃ b, (s k).data = .nullifier b

/-- Decides `d.IsNullifierAccount s k` by comparing the owner and casing on the account data. -/
instance (d : CodeModel.Deployment) (s : CodeModel.State) (k : CodeModel.Pubkey) :
    Decidable (d.IsNullifierAccount s k) := by
  unfold Deployment.IsNullifierAccount
  cases (s k).data <;> simp <;> infer_instance

end PrivacyCash.Model

namespace Connection

/-! ## Values -/

/-- `toBytes l`: turns each code byte (`U8`) into its 8-bit vector, the spec's byte. -/
def toBytes (l : List U8) : Spec.Bytes := l.map (·.bv)

/-- `toF b`: reads 32 bytes as a big-endian number and reduces it mod p, the spec's field
    element. The reduction never applies
    where `toF` is used: public inputs of an accepted `transact` are below p (the verifier
    rejects the rest, `verifyProof_canonical`), and so are the tree's stored roots and subtrees
    (invariant `WellFormed`). -/
def toF (b : Std.Array U8 32#usize) : Spec.F :=
  (Spec.natOfBE (toBytes b.val) : Spec.F)

/-- `Canonical b`: the 32 bytes, read as a big-endian number, are below p, so `toF b`
    does not reduce. With `toF b = x`, this is the spec's
    `canonicalEncoding (toBytes b.val) x`. -/
def Canonical (b : Std.Array U8 32#usize) : Prop :=
  Spec.natOfBE (toBytes b.val) < Spec.p

/-- `toArray n bs`: turns each spec byte into a code byte and packs them into an
    `n`-byte code array; `none` if `bs` does not have exactly `n` bytes. -/
def toArray (n : Usize) (bs : Spec.Bytes) : Option (Std.Array U8 n) :=
  if h : bs.length = n.val then
    some (Std.Array.from (bs.map (fun b => (⟨b⟩ : U8))) (by simp [h]))
  else none

/-- `bytesToArray n bs`: `toArray n bs`, or the all-zero array if `bs` does
    not have exactly `n` bytes. -/
def bytesToArray (n : Usize) (bs : Spec.Bytes) : Std.Array U8 n :=
  (toArray n bs).getD (Std.Array.repeat n 0#u8)

/-- `toPubkey k`: reads the 32 bytes of a Solana address as a little-endian 256-bit number,
    the spec's address. `BitVec.ofNat` reduces mod 2^256, which never applies: a number read
    from 32 bytes is at most 256^32 − 1 = 2^256 − 1 (all bytes 0xFF). -/
def toPubkey (k : CodeModel.Pubkey) : Spec.Pubkey :=
    BitVec.ofNat 256 (Spec.natOfLE (toBytes k.val))

/-- `fromPubkey x`: writes the spec's address (a 256-bit number) as 32 little-endian
    bytes, a Solana address. -/
def fromPubkey (x : Spec.Pubkey) : CodeModel.Pubkey :=
  Std.Array.from (CodeModel.leBytes32 x.toNat) (by simp [CodeModel.leBytes32])

/-! ## The program's accounts -/

/-- `toTree t`: from the tree account `t`, creates a spec tree. The root index is reduced
    mod 100, which never applies: `WellFormed` keeps it below 100. -/
def toTree (t : CodeModel.MerkleTreeAccount) : Spec.Tree where
  nextIndex := t.next_index.val
  subtrees i := toF (t.subtrees.val[i.val]!)
  root := toF t.root
  history i := toF (t.root_history.val[i.val]!)
  rootIndex := Fin.ofNat 100 t.root_index.val

/-- `toConfig c t`: from the config account `c` and the tree account `t`, creates a spec
    config. -/
def toConfig (c : CodeModel.GlobalConfig)
    (t : CodeModel.MerkleTreeAccount) : Spec.config where
  -- In the code, only the config account's authority may change the fee settings
  authority := toPubkey c.authority
  -- In the code, only the tree account's authority may change the deposit limit
  limitAuthority := toPubkey t.authority
  depositFeeRate := c.deposit_fee_rate.val
  withdrawalFeeRate := c.withdrawal_fee_rate.val
  feeErrorMargin := c.fee_error_margin.val
  maxDepositLimit := t.max_deposit_amount.val

/-! ## Worlds -/

/-- `nullifierAccountsOf d s`: collects every address `x` whose account (at
    `fromPubkey x`) is a nullifier account of the program in `s`. -/
def nullifierAccountsOf (d : CodeModel.Deployment) (s : CodeModel.State) :
    Finset Spec.Pubkey :=
  -- From every possible spec address we want the ones that are a nullifier account
  Finset.univ.filter fun x => d.IsNullifierAccount s (fromPubkey x)

/-- `toWorld d rent s`: from the chain state `s`, creates a spec world. `rent` is Solana's
    rent-exempt minimum per account size (`SameRent` ties it to each transaction). -/
def toWorld (d : CodeModel.Deployment) (rent : Nat → U64) (s : CodeModel.State) :
    Spec.World where
  state :=
    { tree := toTree (s.treeAccount d.treeAddress) -- ok
      nullifierAccounts := nullifierAccountsOf d s
      pool := toPubkey d.poolAddress
      nullifierAddr i b :=
        match toArray 32#usize b with
        -- `b` is a nullifier (32 bytes): the address of its PDA
        | some n => toPubkey (d.nullifierAddress i n)
        -- `b` is not 32 bytes long: does not occur, since `transact` requires 32-byte public
        -- inputs (precondition `canonicalInputs`) and the code's nullifiers are `[u8; 32]`
        | none => 0
      config := toConfig (s.configAccount d.configAddress)
                  (s.treeAccount d.treeAddress)
      treeAccount := toPubkey d.treeAddress
      configAccount := toPubkey d.configAddress }
  balances x := s.lamports (fromPubkey x)
  -- The lamports the pool must keep to stay on chain (Solana's minimum for the pool's size)
  rentExemptMin := (rent CodeModel.treeTokenAccountSpace).val
  -- The lamports a new nullifier account must hold (Solana's minimum for its size)
  nullifierRent := (rent CodeModel.nullifierAccountSpace).val

/-! ## Transactions -/

/-- `TransactArgs`: the instruction data of a `transact`, the arguments of the program's
    `transact` after `ctx` (lib.rs): the proof, the external amount and fee
    (`ext_data_minified`), and the two encrypted outputs. -/
structure TransactArgs where
  /-- The Groth16 proof and its seven public inputs, as bytes. -/
  proof : CodeModel.Proof
  /-- The external amount: positive deposits, negative withdraws. -/
  extAmount : I64
  /-- The relayer's fee. -/
  fee : U64
  /-- The first encrypted output. -/
  encryptedOutput1 : Slice U8
  /-- The second encrypted output. -/
  encryptedOutput2 : Slice U8

/-- `TransactTx`: a `transact` as the sender sends it: everything the sender chooses. -/
structure TransactTx where
  /-- Who signs. -/
  ctx : CodeModel.TxContext
  /-- The accounts listed (the program's `Context<Transact>`). -/
  accounts : CodeModel.TransactAccounts
  /-- The instruction data. -/
  args : TransactArgs

/-- `tx.instruction`: packs `tx`'s accounts and instruction data into the code model's
    `transact` instruction. -/
abbrev TransactTx.instruction (tx : TransactTx) : CodeModel.Instruction :=
  .transact tx.accounts tx.args.proof tx.args.extAmount tx.args.fee tx.args.encryptedOutput1
    tx.args.encryptedOutput2

/-- `tx.env sysvarRent`: builds the environment the runtime gives `tx`: its signers, and the
    `Rent` sysvar as the runtime reads it (`sysvarRent`), which the sender does not choose. -/
abbrev TransactTx.env (tx : TransactTx) (sysvarRent : Option (Nat → U64)) : CodeModel.TxEnv :=
  { tx.ctx with minimumBalance := sysvarRent }

/-- `toInputs tx`: from a `transact` as sent, creates spec transaction inputs. `toF` reduces
    mod p, which never applies on an accepted `transact`: the verifier rejects public inputs
    `≥ p` (`verifyProof_canonical`). -/
def toInputs (tx : TransactTx) : Spec.TxInputs where
  R := toF tx.args.proof.root
  pubAmt := toF tx.args.proof.public_amount
  extDataHash := toF tx.args.proof.ext_data_hash
  k0 := toF tx.args.proof.input_nullifiers.val[0]!
  k1 := toF tx.args.proof.input_nullifiers.val[1]!
  outC0 := toF tx.args.proof.output_commitments.val[0]!
  outC1 := toF tx.args.proof.output_commitments.val[1]!
  extAmt := tx.args.extAmount.val
  f := tx.args.fee.val
  -- the account listed as `signer`, which pays deposits
  s := toPubkey tx.accounts.signer
  -- the keys that signed the transaction, as the runtime reports them
  signers := tx.ctx.signers.map toPubkey
  A := toPubkey tx.accounts.recipient
  t := toPubkey tx.accounts.feeRecipientAccount
  encOut0 := toBytes tx.args.encryptedOutput1.val
  encOut1 := toBytes tx.args.encryptedOutput2.val
  π := ⟨toBytes tx.args.proof.proof_a.val, toBytes tx.args.proof.proof_b.val,
    toBytes tx.args.proof.proof_c.val⟩
  mintAddr := toPubkey CodeModel.SOL_ADDRESS
  pubInputBytes i := toBytes ((CodeModel.publicInputs tx.args.proof)[i.val]!).val

/-- `Accepts d s txEnv ix`: `step` runs instruction `ix` in the transaction environment `txEnv`
    on the chain state `s` without error. -/
def Accepts (d : CodeModel.Deployment) (s : CodeModel.State) (txEnv : CodeModel.TxEnv)
    (ix : CodeModel.Instruction) : Prop :=
  ∃ s' emitted, CodeModel.step d s txEnv ix = .ok (s', emitted)

/-! ## Spec proofs as code proofs (completeness over runs)

The other direction: a spec run's transaction becomes the code's proof argument. `toInputs`
undoes this (proved under the spec's preconditions); `run_complete_except_L1_A0` names the
address collisions of the code proofs obtained this way. -/

/-- `fromSpecProof inputs`: from spec transaction inputs, creates the code's proof argument. -/
def fromSpecProof (inputs : Spec.TxInputs) : CodeModel.Proof where
  proof_a := bytesToArray 64#usize inputs.π.A
  proof_b := bytesToArray 128#usize inputs.π.B
  proof_c := bytesToArray 64#usize inputs.π.C
  root := bytesToArray 32#usize (inputs.pubInputBytes 0)
  public_amount := bytesToArray 32#usize (inputs.pubInputBytes 1)
  ext_data_hash := bytesToArray 32#usize (inputs.pubInputBytes 2)
  input_nullifiers := Std.Array.make 2#usize
    [bytesToArray 32#usize (inputs.pubInputBytes 3), bytesToArray 32#usize (inputs.pubInputBytes 4)]
  output_commitments := Std.Array.make 2#usize
    [bytesToArray 32#usize (inputs.pubInputBytes 5), bytesToArray 32#usize (inputs.pubInputBytes 6)]

/-! ## Executions

An execution from `s₀` is its events `evs` (core-model's `Event`: a program instruction in a
transaction, or an outside action) and the chain state after each (`states`, recorded by
`ExecutionPath`). Positions count from 0: event `i` takes the chain from `stateAt s₀ states i`
to `stateAt s₀ states (i+1)`. -/

/-- `ExecutionPath d s evs states s'`: core-model's `Run` from `s` to `s'` over the events
    `evs`, also recording the chain state after each event in `states` (a `Prop` such as `Run`
    cannot hand the states back). Same steps and premises as `Run` (`execution_path_iff_run`). -/
inductive ExecutionPath (d : CodeModel.Deployment) :
    CodeModel.State → List CodeModel.Event → List CodeModel.State → CodeModel.State → Prop where
  | nil (s : CodeModel.State) : ExecutionPath d s [] [] s
  | program {s s' s'' : CodeModel.State} {txEnv : CodeModel.TxEnv} {ix : CodeModel.Instruction}
      {emitted : List CodeModel.CommitmentData} {events : List CodeModel.Event}
      {states : List CodeModel.State} :
      CodeModel.step d s txEnv ix = .ok (s', emitted) → txEnv.RentPositive →
      ExecutionPath d s' events states s'' →
        ExecutionPath d s (.program txEnv ix emitted :: events) (s' :: states) s''
  | env {s s' s'' : CodeModel.State} {events : List CodeModel.Event}
      {states : List CodeModel.State} :
      CodeModel.EnvStep d.programId s s' → ExecutionPath d s' events states s'' →
        ExecutionPath d s (.env :: events) (s' :: states) s''

/-- `stateAt s₀ states i`: looks up the chain state after the first `i` events: `s₀` for
    `i = 0`, else entry `i - 1` of `states`. -/
def stateAt (s₀ : CodeModel.State) (states : List CodeModel.State) (i : ℕ) : CodeModel.State :=
  (s₀ :: states).getD i s₀

/-- `stepTxs txEnv ix`: lists the spec transactions of instruction `ix`: for a `transact`, its
    inputs (`toInputs`); for any other instruction none, since the spec treats them as changes
    between transactions. -/
def stepTxs (txEnv : CodeModel.TxEnv) : CodeModel.Instruction → List Spec.TxInputs
  | .transact a proof ext fee out1 out2 => [toInputs ⟨txEnv.toTxContext, a, ⟨proof, ext, fee, out1, out2⟩⟩]
  | _ => []

/-- `runTxs evs`: collects the spec transactions of the program instructions in `evs`, in order
    (`stepTxs`); outside actions contribute none. -/
def runTxs : List CodeModel.Event → List Spec.TxInputs
  | [] => []
  | .program txEnv ix _ :: es => stepTxs txEnv ix ++ runTxs es
  | .env :: es => runTxs es

/-- `IsInitializeAt evs k txEnv a`: event `k` is the program instruction `initialize` with
    accounts `a`, run in the transaction environment `txEnv`. -/
def IsInitializeAt (evs : List CodeModel.Event) (k : ℕ) (txEnv : CodeModel.TxEnv)
    (a : CodeModel.InitializeAccounts) : Prop :=
  ∃ em, evs[k]? = some (.program txEnv (.initialize a) em)

/-- `toAdminChange d before txEnv ix`: from the admin instruction `ix`, creates a spec admin
    change; `none` for other instructions. A fee setting `update_global_config` omits keeps its
    value in the chain state `before` the instruction. -/
def toAdminChange (d : CodeModel.Deployment) (before : CodeModel.State) (txEnv : CodeModel.TxEnv) :
    CodeModel.Instruction → Option Spec.AdminChange
  | .updateDepositLimit _ newLimit =>
    some ⟨txEnv.signers.map toPubkey, .depositLimit newLimit.val⟩
  | .updateGlobalConfig _ dep wd margin =>
    let c := before.configAccount d.configAddress
    some ⟨txEnv.signers.map toPubkey, .feeSettings (dep.getD c.deposit_fee_rate).val
      (wd.getD c.withdrawal_fee_rate).val (margin.getD c.fee_error_margin).val⟩
  | _ => none

/-- `adminChangesBefore d s₀ evs states i`: collects the admin changes (`toAdminChange`) of the
    admin instructions among the first `i` events, in order, each read on the chain state just
    before it. -/
def adminChangesBefore (d : CodeModel.Deployment) (s₀ : CodeModel.State) (evs : List CodeModel.Event)
    (states : List CodeModel.State) (i : ℕ) : List Spec.AdminChange :=
  (List.range i).flatMap fun k =>
    match evs.getD k .env with
    | .program txEnv ix _ => (toAdminChange d (stateAt s₀ states k) txEnv ix).toList
    | .env => []

/-- `Initialized d s`: `initialize` has run: the program holds its tree, pool and config at
    their canonical addresses. -/
def Initialized (d : CodeModel.Deployment) (s : CodeModel.State) : Prop :=
  (∃ t, CodeModel.HoldsTree d.programId s d.treeAddress t) ∧
    (∃ p, CodeModel.HoldsTreeToken d.programId s d.poolAddress p) ∧
    (∃ c, CodeModel.HoldsGlobalConfig d.programId s d.configAddress c)

/-- `NoProgramAccounts d s`: at no address does the program hold a tree, pool, config or
    nullifier account in `s`. -/
def NoProgramAccounts (d : CodeModel.Deployment) (s : CodeModel.State) : Prop :=
  (∀ k t, ¬ CodeModel.HoldsTree d.programId s k t) ∧
    (∀ k p, ¬ CodeModel.HoldsTreeToken d.programId s k p) ∧
    (∀ k c, ¬ CodeModel.HoldsGlobalConfig d.programId s k c) ∧
    ∀ k, ¬ d.IsNullifierAccount s k

/-! ## Executions as spec runs -/

/-- `RunOfDeployment d rent params`: the spec run's start parameters `params` use this
    deployment's addresses, its rents (`rent` at each account's size) and its admin key. The
    rest (config, balances, initializer, signers) is free. -/
structure RunOfDeployment (d : CodeModel.Deployment) (rent : Nat → U64)
    (params : Spec.InitParams) : Prop where
  /-- The pool is the deployment's pool. -/
  pool : params.pool = toPubkey d.poolAddress
  /-- The nullifier accounts are at the program's derived addresses, as `toWorld` reads them
      (the same in every state `s`). -/
  nullifierAddr : ∀ s, params.nullifierAddr = (toWorld d rent s).state.nullifierAddr
  /-- The tree's account is the deployment's. -/
  treeAccount : params.treeAccount = toPubkey d.treeAddress
  /-- The config's account is the deployment's. -/
  configAccount : params.configAccount = toPubkey d.configAddress
  /-- The pool's rent is Solana's for its size. -/
  rentExemptMin : params.rentExemptMin = (rent CodeModel.treeTokenAccountSpace).val
  /-- A nullifier account's rent is Solana's for its size. -/
  nullifierRent : params.nullifierRent = (rent CodeModel.nullifierAccountSpace).val
  /-- The tree account's rent is Solana's for its size. -/
  treeRent : params.treeRent = (rent CodeModel.treeAccountSpace).val
  /-- The config account's rent is Solana's for its size. -/
  configRent : params.configRent = (rent CodeModel.globalConfigSpace).val
  /-- The admin key is the deployment's (`ADMIN_PUBKEY`). -/
  admin : params.admin = d.adminPubkey.map toPubkey

/-- `StartsFromInit params txEnv a w`: the spec run's start parameters `params` are what
    `initialize` (accounts `a`, transaction environment `txEnv`) set up, with `w` the spec world
    right after it. -/
structure StartsFromInit (params : Spec.InitParams) (txEnv : CodeModel.TxEnv)
    (a : CodeModel.InitializeAccounts) (w : Spec.World) : Prop where
  /-- The initializer is the authority `initialize` named. -/
  initializer : params.initializer = toPubkey a.authority
  /-- The signers are those of `initialize`'s transaction. -/
  signers : params.signers = txEnv.signers.map toPubkey
  /-- The config is the one `initialize` wrote. -/
  config : params.cfg = w.state.config
  /-- Every account starts with its balance right after `initialize`, except the three it
      creates, whose balances (their rents) `initWorld` sets itself. -/
  balances : ∀ x ∉ ({params.pool, params.treeAccount, params.configAccount} : Set Spec.Pubkey),
    params.balances x = w.balances x

/-- `TxRecord`: what the spec sees of one transaction: its inputs, the pool balance just before
    it, the state and the pool balance right after it, and all admin changes before it. Other
    balances are not recorded: the spec's `transact` sets them, and the next change between
    transactions starts from the chain's. -/
structure TxRecord where
  /-- The transaction's inputs. -/
  inputs : Spec.TxInputs
  /-- The pool's balance just before the transaction. -/
  poolBefore : ℕ
  /-- The spec state just after the transaction. -/
  stateAfter : Spec.State
  /-- The pool's balance just after the transaction. -/
  poolAfter : ℕ
  /-- All admin changes before the transaction, in order. -/
  adminChangesBefore : List Spec.AdminChange

/-- `executionTxRecords d rent s₀ evs states`: collects the record of each accepted `transact`
    of the execution, in order. For the `transact` at position `i`: its inputs (`toInputs`), the
    pool balance before it, the spec state and pool balance after it (read from `stateAt`), and
    the admin changes of the events before it (`adminChangesBefore`). -/
def executionTxRecords (d : CodeModel.Deployment) (rent : Nat → U64) (s₀ : CodeModel.State)
    (evs : List CodeModel.Event) (states : List CodeModel.State) : List TxRecord :=
  (List.range evs.length).flatMap fun i =>
    match evs[i]? with
    | some (CodeModel.Event.program txEnv (.transact a proof ext fee out1 out2) _) =>
      [{ inputs := toInputs ⟨txEnv.toTxContext, a, ⟨proof, ext, fee, out1, out2⟩⟩
         poolBefore := (stateAt s₀ states i).lamports d.poolAddress
         stateAfter := (toWorld d rent (stateAt s₀ states (i+1))).state
         poolAfter := (stateAt s₀ states (i+1)).lamports d.poolAddress
         adminChangesBefore := adminChangesBefore d s₀ evs states i }]
    | _ => []

section
variable [Spec.PoseidonHashes] [Spec.Sha] [Spec.Groups] [AddCommGroup Spec.G1]
  [Module Spec.F Spec.G1]
  [CommGroup Spec.GT] [Spec.Pairing] [Spec.Deployment]

/-- `runTxRecords r pool`: collects the record of each transaction of the spec run `r`, in
    order. For transaction `j`: its inputs, the balance of `pool` after the change between
    transactions before it, the state and pool balance of world `j+1`, and the admin changes up
    to it. -/
def runTxRecords {w₀ : Spec.World} (r : Spec.Run w₀) (pool : Spec.Pubkey) :
    List TxRecord :=
  r.txs.mapIdx fun j tx =>
    { inputs := tx
      poolBefore := (r.updatedValues j).balances pool
      stateAfter := (r.ws (j+1)).state
      poolAfter := (r.ws (j+1)).poolBalance
      adminChangesBefore := r.adminChangesUpTo (j+1) }

/-- `IsRunOf d rent s₀ evs states s params r`: the spec run `r` from `initWorld params`
    describes the execution `evs` from `s₀` through `states` to `s`: same deployment, same start,
    same transactions, same end. -/
structure IsRunOf (d : CodeModel.Deployment) (rent : Nat → U64) (s₀ : CodeModel.State)
    (evs : List CodeModel.Event) (states : List CodeModel.State) (s : CodeModel.State)
    (params : Spec.InitParams)
    (r : Spec.Run (Spec.initWorld params)) : Prop where
  /-- The deployment: `params` names this deployment's addresses, rents and admin key. -/
  deployment : RunOfDeployment d rent params
  /-- The start: `r` starts from what the last `initialize` (event `k`) set up. -/
  start : ∃ k txEnv a, IsInitializeAt evs k txEnv a ∧
    (∀ k' txEnv' a', IsInitializeAt evs k' txEnv' a' → k' ≤ k) ∧
    StartsFromInit params txEnv a (toWorld d rent (stateAt s₀ states (k+1)))
  /-- The transactions: one by one, `r`'s transactions are the execution's accepted `transact`s,
      with the chain's pool balance before, state and pool balance after, and admin changes
      before. So `r.donated` is what the pool received from outside. -/
  transactions :
    runTxRecords r (toPubkey d.poolAddress) = executionTxRecords d rent s₀ evs states
  /-- The end: `s` is `r`'s final world after an allowed change, which records the admin
      instructions since the last transaction. -/
  final : ∃ b : Spec.UpdatedValuesBetweenTransacts, b.Allowed r.final ∧
    r.adminChangesUpTo r.txs.length ++ b.adminChanges = adminChangesBefore d s₀ evs states evs.length ∧
    toWorld d rent s = r.final.withUpdatedValues b

/-- `IsSpecRun d rent s₀ evs states s`: some spec run describes the execution (`IsRunOf`). -/
def IsSpecRun (d : CodeModel.Deployment) (rent : Nat → U64) (s₀ : CodeModel.State)
    (evs : List CodeModel.Event) (states : List CodeModel.State) (s : CodeModel.State) : Prop :=
  ∃ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params)),
    IsRunOf d rent s₀ evs states s params r

end

/-! ## The verifier: the spec instantiated by the syscalls and the program's key

For the verifier bridge: the spec's groups, decoding and pairing come from the syscall
contracts `C` (core-model's `AltBn128Contracts`), its key from the program's `VERIFYING_KEY`. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] {s : CodeModel.AltBn128}
open PrivacyCash.Proofs.Groth16 (ic)

/-- `syscallGroups C`: instantiates the spec's groups with the syscalls' `G1`, `G2`, `GT`,
    decoding a G1 point from 64 bytes with `C.decodeG1` and a G2 point from 128 bytes with
    `C.decodeG2`; bytes of another length decode to no point. -/
@[reducible] def syscallGroups (C : CodeModel.AltBn128Contracts s G1 G2 GT) : Spec.Groups :=
  ⟨G1, G2, GT, fun bs => (toArray 64#usize bs).bind C.decodeG1,
    fun bs => (toArray 128#usize bs).bind C.decodeG2⟩

/-- `syscallPairing C`: instantiates the spec's pairing with the syscall's pairing `C.e`. -/
@[reducible] def syscallPairing (C : CodeModel.AltBn128Contracts s G1 G2 GT) :
    @Spec.Pairing (syscallGroups C) :=
  @Spec.Pairing.mk (syscallGroups C) C.e

/-- `programKey C`: decodes the program's constant `VERIFYING_KEY` with the syscalls into the
    spec's verification key. A point that does not decode becomes the default point, which never
    applies: whenever the verifier accepts, every key point decodes (`programVerifier_groth16`). -/
@[reducible] def programKey (C : CodeModel.AltBn128Contracts s G1 G2 GT) :
    @Spec.Groth16.VerificationKey (syscallGroups C) :=
  letI : Spec.Groups := syscallGroups C
  let vk := CodeModel.VERIFYING_KEY
  { α := (C.decodeG1 vk.vk_alpha_g1).getD 0, β := (C.decodeG2 vk.vk_beta_g2).getD default,
    γ := (C.decodeG2 vk.vk_gamme_g2).getD default, δ := (C.decodeG2 vk.vk_delta_g2).getD default,
    IC := fun i => ic C vk i.val }

/-- `programDeployment C`: instantiates the spec's deployment with the program's key
    (`programKey C`) and its SOL mint address `SOL_ADDRESS`. -/
@[reducible] def programDeployment (C : CodeModel.AltBn128Contracts s G1 G2 GT) :
    @Spec.Deployment (syscallGroups C) :=
  @Spec.Deployment.mk (syscallGroups C) (programKey C) (toPubkey CodeModel.SOL_ADDRESS)

/-- `withSyscallSpec C in t`: the term `t`, with the spec instantiated by the syscalls `C` and
    the program's key (groups `syscallGroups C`, pairing `syscallPairing C`, deployment
    `programDeployment C`). Shorthand for the three `letI`s that set these instances. -/
macro "withSyscallSpec " C:term:max " in " t:term : term =>
  `(letI : Spec.Groups := syscallGroups $C
    letI : Spec.Pairing := syscallPairing $C
    letI : Spec.Deployment := programDeployment $C
    $t)

/-- `SpecAllows C rent s tx`: every precondition of the spec's `transact` holds for `tx`'s
    inputs (`toInputs tx`) in the world `toWorld d rent s`, with the spec instantiated by the
    syscalls and the program's key. -/
def SpecAllows {d : CodeModel.Deployment}
    (C : CodeModel.AltBn128Contracts d.crypto.altBn128 G1 G2 GT) [Spec.PoseidonHashes] [Spec.Sha] (rent : Nat → U64) (s : CodeModel.State)
    (tx : TransactTx) : Prop :=
  withSyscallSpec C in
  Spec.transactPreconditions (toInputs tx) (toWorld d rent s)

/-- `SpecRun C params`: the type of spec runs from `initWorld params`, with the spec
    instantiated by the syscalls and the program's key. -/
abbrev SpecRun (C : CodeModel.AltBn128Contracts s G1 G2 GT) [Spec.PoseidonHashes] [Spec.Sha]
    (params : Spec.InitParams) : Type :=
  withSyscallSpec C in
  Spec.Run (Spec.initWorld params)

/-- `r.txs`: the transactions of the spec run `r`, in order. -/
abbrev SpecRun.txs {C : CodeModel.AltBn128Contracts s G1 G2 GT}
    [Spec.PoseidonHashes] [Spec.Sha] {params : Spec.InitParams} (r : SpecRun C params) : List Spec.TxInputs :=
  withSyscallSpec C in
  Spec.Run.txs r

end

end Connection
