import PrivacyCash
import Spec.Statements
import Mathlib.Data.FinEnum
open Aeneas Aeneas.Std

/-! # Mapping: code-model values to spec values

REVIEW SURFACE. How code values, chain states and code runs map to the spec's. The connection
theorems (`ConnectionTheorems.lean`) mean what these definitions say, so each is short.

A map that loses information makes a theorem weaker. Every map below is injective on the
values that matter, except where its docstring says otherwise (field elements are read mod p).

Names say where they come from:
- `Spec.…`: the spec.
- `CodeModel.…`: core-model (aliases, below).
- dot notation on a deployment `d` or a chain state `s` (`d.treeAddress`, `s.lamports k`): reads a
  value out of the code model; defined here (see "Readers"), the result is still a code value.
- no prefix: defined here, mostly maps between code and spec values (`toWorld`, `fromPubkey`, …).

Each map's docstring states its direction right after its name: (Code Model → spec) or
(spec → Code Model).
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
on a deployment `d` or a chain state `s`. -/
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
    holds no config, which `WellFormed` rules out at the config's address. -/
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

/-- `toBytes l` (Code Model → spec): turns each code byte (`U8`) into its 8-bit vector, the spec's byte. -/
def toBytes (l : List U8) : Spec.Bytes := l.map (·.bv)

/-- `toF b` (Code Model → spec): reads 32 bytes as a big-endian number and reduces it mod p, the
    spec's field element. The reduction never applies where `toF` is used: public inputs of an
    accepted `transact` instruction are below p (the verifier rejects the rest,
    `verifyProof_canonical`), and so are the tree's stored roots and subtrees (invariant
    `WellFormed`). -/
def toF (b : Std.Array U8 32#usize) : Spec.F :=
  (Spec.natOfBE (toBytes b.val) : Spec.F)

/-- `Canonical b`: the 32 bytes, read as a big-endian number, are below p, so `toF b`
    does not reduce. With `toF b = x`, this is the spec's
    `canonicalEncoding (toBytes b.val) x`. -/
def Canonical (b : Std.Array U8 32#usize) : Prop :=
  Spec.natOfBE (toBytes b.val) < Spec.p

/-- `toArray n bs` (spec → Code Model): turns each spec byte into a code byte and packs them
    into an `n`-byte code array; `none` if `bs` does not have exactly `n` bytes. -/
def toArray (n : Usize) (bs : Spec.Bytes) : Option (Std.Array U8 n) :=
  if h : bs.length = n.val then
    some (Std.Array.from (bs.map (fun b => (⟨b⟩ : U8))) (by simp [h]))
  else none

/-- `bytesToArray n bs` (spec → Code Model): `toArray n bs`, or the all-zero array if `bs`
    does not have exactly `n` bytes, which `canonicalInputs` (32-byte public inputs) and the
    point decoding of `syscallGroups` (64/128-byte proof points) rule out in a spec run. -/
def bytesToArray (n : Usize) (bs : Spec.Bytes) : Std.Array U8 n :=
  (toArray n bs).getD (Std.Array.repeat n 0#u8)

/-- `toPubkey k` (Code Model → spec): reads the 32 bytes of a Solana address as a little-endian
    256-bit number, the spec's address. `BitVec.ofNat` reduces mod 2^256, which never applies: a
    number read from 32 bytes is at most 256^32 − 1 = 2^256 − 1 (all bytes 0xFF). -/
def toPubkey (k : CodeModel.Pubkey) : Spec.Pubkey :=
    BitVec.ofNat 256 (Spec.natOfLE (toBytes k.val))

/-- `fromPubkey x` (spec → Code Model): writes the spec's address (a 256-bit number) as 32
    little-endian bytes, a Solana address. -/
def fromPubkey (x : Spec.Pubkey) : CodeModel.Pubkey :=
  Std.Array.from (CodeModel.leBytes32 x.toNat) (by simp [CodeModel.leBytes32])

/-! ## The program's accounts -/

/-- `toTree t` (Code Model → spec): from the tree account `t`, creates a spec tree. The root
    index is reduced mod 100, which never applies: `WellFormed` keeps it below 100. -/
def toTree (t : CodeModel.MerkleTreeAccount) : Spec.Tree where
  nextIndex := t.next_index.val
  subtrees i := toF (t.subtrees.val[i.val]!)
  root := toF t.root
  history i := toF (t.root_history.val[i.val]!)
  rootIndex := Fin.ofNat 100 t.root_index.val

/-- `toConfig c t` (Code Model → spec): from the config account `c` and the tree account `t`,
    creates a spec config. -/
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

/-- `nullifierAccountsOf d s` (Code Model → spec): collects every spec address `x` whose
    account (at `fromPubkey x`) is a nullifier account of the program in the chain state `s`. -/
def nullifierAccountsOf (d : CodeModel.Deployment) (s : CodeModel.State) :
    Finset Spec.Pubkey :=
  -- From every possible spec address we want the ones that are a nullifier account
  Finset.univ.filter fun x => d.IsNullifierAccount s (fromPubkey x)

/-- `toWorld d rent s` (Code Model → spec): from the chain state `s`, creates a spec world.
    `rent` is Solana's rent-exempt minimum per account size (`SameRent` ties it to each Solana
    transaction). -/
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
        -- `b` is not 32 bytes long: does not occur, since the spec's `transact` requires 32-byte
        -- public inputs (precondition `canonicalInputs`) and the code's nullifiers are `[u8; 32]`
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

/-! ## `transact` instructions -/

/-- `TransactArgs`: the instruction data of a `transact` instruction, the arguments of
    `transact` in lib.rs after `ctx`: the proof, the external amount and fee
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

/-- `TransactTx`: a `transact` instruction as the sender sends it: everything the sender
    chooses. -/
structure TransactTx where
  /-- Who signs the Solana transaction. -/
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

/-- `toInputs tx` (Code Model → spec): from a `transact` instruction as sent, creates a spec
    transaction. `toF` reduces mod p, which never applies on an accepted `transact` instruction:
    the verifier rejects public inputs `≥ p` (`verifyProof_canonical`). -/
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
  -- the keys that signed the Solana transaction, as the runtime reports them
  signers := tx.ctx.signers.map toPubkey
  A := toPubkey tx.accounts.recipient
  t := toPubkey tx.accounts.feeRecipientAccount
  encOut0 := toBytes tx.args.encryptedOutput1.val
  encOut1 := toBytes tx.args.encryptedOutput2.val
  π := ⟨toBytes tx.args.proof.proof_a.val, toBytes tx.args.proof.proof_b.val,
    toBytes tx.args.proof.proof_c.val⟩
  mintAddr := toPubkey CodeModel.SOL_ADDRESS
  pubInputBytes i := toBytes ((CodeModel.publicInputs tx.args.proof)[i.val]!).val

/-- `Accepts d s txEnv ix`: `step` runs instruction `ix` in the Solana transaction's environment
    `txEnv` on the chain state `s` without error. -/
def Accepts (d : CodeModel.Deployment) (s : CodeModel.State) (txEnv : CodeModel.TxEnv)
    (ix : CodeModel.Instruction) : Prop :=
  ∃ s' emitted, CodeModel.step d s txEnv ix = .ok (s', emitted)

/-! ## Spec proofs as code proofs (completeness over runs)

The other direction: a spec run's spec transaction becomes the code's proof argument. `toInputs`
undoes this (proved under the spec's preconditions); `run_complete_except_L1_A0` names the
address collisions of the code proofs obtained this way. -/

/-- `fromSpecProof inputs` (spec → Code Model): from a spec transaction, creates the code's
    proof argument. -/
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

/-! ## Code runs

A code run is a list of steps (`RunStep`). Each step is an event (the Code Model's `Event`: a
program instruction in a Solana transaction, or an outside action) together with the chain states
just before and just after it. `CodeRun` says that the steps form a run of the Code Model: each
event can take the chain from its state before to its state after, and each step starts where the
one before it ended. -/

/-- One event of a code run: `EventStep d before event after` holds when `event` can take the
    chain from state `before` to state `after`, as the Code Model's `Run` requires. -/
def EventStep (d : CodeModel.Deployment) (before : CodeModel.State) :
    CodeModel.Event → CodeModel.State → Prop
    -- A call to the Privacy Cash program (`Run.program`): holds when `step` would accept it in
    -- `before` with result `after` and logged events `emitted`, and when the rent is positive.
  | .program txEnv ix emitted, after =>
      CodeModel.step d before txEnv ix = .ok (after, emitted) ∧ txEnv.RentPositive
    -- Anything outside of the program that happens (`Run.env`): holds when `EnvStep`
    -- allows `after` to follow `before`.
  | .env, after => CodeModel.EnvStep d.programId before after

/-- One step of a code run: `event` took the chain from state `before` to state `after`. -/
structure RunStep where
  /-- The chain state just before the event. -/
  before : CodeModel.State
  /-- The event: a program instruction or an outside action. -/
  event : CodeModel.Event
  /-- The chain state just after the event. -/
  after : CodeModel.State

/-- `eventsOf steps`: lists the events of the steps `steps`, in order. -/
def eventsOf (steps : List RunStep) : List CodeModel.Event :=
  steps.map RunStep.event

/-- `CodeRun d s₀ steps sₙ`: the steps `steps` form a code run from `s₀` to `sₙ`: the Code
    Model's `Run` over their events, with the chain states before and after each event recorded.

    The two constructors give the cases in which this holds:
    - `nil`: the empty list is a code run from any state to itself;
    - `cons`: `⟨s₀, event, s₁⟩ :: steps` is a code run from `s₀` to `sₙ` if `event` can take
      the chain from `s₀` to `s₁` (`EventStep`) and `steps` is a code run from `s₁` to `sₙ`.

    `codeRun_iff_run` proves that `CodeRun` and `Run` have the same code runs. -/
inductive CodeRun (d : CodeModel.Deployment) :
    CodeModel.State → List RunStep → CodeModel.State → Prop where
  | nil (s₀ : CodeModel.State) : CodeRun d s₀ [] s₀
  | cons {s₀ s₁ sₙ : CodeModel.State} {event : CodeModel.Event} {steps : List RunStep} :
      -- `s₁` is the state recorded after the first step; the code run over `steps` starts there.
      EventStep d s₀ event s₁ →
      CodeRun d s₁ steps sₙ →
        CodeRun d s₀ (⟨s₀, event, s₁⟩ :: steps) sₙ

/-- `stepTxs txEnv ix` (Code Model → spec): lists the spec transactions of instruction `ix`: for
    a `transact` instruction, its spec transaction (`toInputs`); for any other instruction none,
    since the spec treats them as changes between spec transactions. -/
def stepTxs (txEnv : CodeModel.TxEnv) : CodeModel.Instruction → List Spec.TxInputs
  | .transact a proof ext fee out1 out2 =>
    [toInputs ⟨txEnv.toTxContext, a, ⟨proof, ext, fee, out1, out2⟩⟩]
  | _ => []

/-- `runTxs events` (Code Model → spec): collects the spec transactions of the program
    instructions in `events`, in order (`stepTxs`); outside actions contribute none. -/
def runTxs : List CodeModel.Event → List Spec.TxInputs
  | [] => []
  | .program txEnv ix _ :: es => stepTxs txEnv ix ++ runTxs es
  | .env :: es => runTxs es

/-- `TransactIn events txEnv proof`: the code run `events` accepted a `transact` instruction with
    proof `proof`, in the Solana transaction's environment `txEnv`. -/
def TransactIn (events : List CodeModel.Event) (txEnv : CodeModel.TxEnv)
    (proof : CodeModel.Proof) : Prop :=
  ∃ a ext fee out1 out2 em,
    CodeModel.Event.program txEnv (.transact a proof ext fee out1 out2) em ∈ events

/-- `proofsIn events`: the proofs of the `transact` instructions the code run `events` accepted. -/
def proofsIn (events : List CodeModel.Event) : Set CodeModel.Proof :=
  {proof | ∃ txEnv, TransactIn events txEnv proof}

/-- `step.IsInitialize txEnv a`: the step's event is the program instruction `initialize` with
    accounts `a`, run in the Solana transaction's environment `txEnv`. -/
def RunStep.IsInitialize (step : RunStep) (txEnv : CodeModel.TxEnv)
    (a : CodeModel.InitializeAccounts) : Prop :=
  ∃ emitted, step.event = .program txEnv (.initialize a) emitted

/-- `toAdminChange d before txEnv ix` (Code Model → spec): from the admin instruction `ix`,
    creates a spec admin change; `none` for other instructions. A fee setting
    `update_global_config` omits keeps its value in the chain state `before` the instruction. -/
def toAdminChange (d : CodeModel.Deployment) (before : CodeModel.State) (txEnv : CodeModel.TxEnv) :
    CodeModel.Instruction → Option Spec.AdminChange
  | .updateDepositLimit _ newLimit =>
    some ⟨txEnv.signers.map toPubkey, .depositLimit newLimit.val⟩
  | .updateGlobalConfig _ dep wd margin =>
    let c := before.configAccount d.configAddress
    some ⟨txEnv.signers.map toPubkey, .feeSettings (dep.getD c.deposit_fee_rate).val
      (wd.getD c.withdrawal_fee_rate).val (margin.getD c.fee_error_margin).val⟩
  | _ => none

/-- `adminChanges d steps` (Code Model → spec): collects the spec admin changes
    (`toAdminChange`) of the admin instructions among `steps`, in order, each read on the chain
    state just before it. -/
def adminChanges (d : CodeModel.Deployment) (steps : List RunStep) : List Spec.AdminChange :=
  steps.flatMap fun step =>
    match step.event with
    | .program txEnv ix _ => (toAdminChange d step.before txEnv ix).toList
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

/-! ## Code runs as spec runs -/

/-- `RunOfDeployment d rent params`: the spec run's start parameters `params` use this
    deployment's addresses, its rents (`rent` at each account's size) and its admin key. The
    rest (config, balances, initializer, signers) is free. -/
structure RunOfDeployment (d : CodeModel.Deployment) (rent : Nat → U64)
    (params : Spec.InitParams) : Prop where
  /-- The pool account is the deployment's. -/
  pool : params.pool = toPubkey d.poolAddress
  /-- The nullifier accounts are at the program's derived addresses, as `toWorld` reads them
      (the same in every chain state `s`). -/
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
    `initialize` (accounts `a`, Solana transaction's environment `txEnv`) set up, with `w` the spec
    world right after it. -/
structure StartsFromInit (params : Spec.InitParams) (txEnv : CodeModel.TxEnv)
    (a : CodeModel.InitializeAccounts) (w : Spec.World) : Prop where
  /-- The initializer is the authority `initialize` named. -/
  initializer : params.initializer = toPubkey a.authority
  /-- The signers are those of `initialize`'s Solana transaction. -/
  signers : params.signers = txEnv.signers.map toPubkey
  /-- The config is the one `initialize` wrote. -/
  config : params.cfg = w.state.config
  /-- Every account starts with its balance right after `initialize`, except the three it
      creates, whose balances (their rents) `initWorld` sets itself. -/
  balances : ∀ x ∉ ({params.pool, params.treeAccount, params.configAccount} : Set Spec.Pubkey),
    params.balances x = w.balances x

/-- `TxRecord`: what the spec sees of one spec transaction: its inputs, the pool's balance just
    before it, the spec state and the pool's balance right after it, and all admin changes before
    it. Other balances are not recorded: the spec's `transact` sets them, and the next change
    between spec transactions starts from the chain's. -/
structure TxRecord where
  /-- The spec transaction. -/
  inputs : Spec.TxInputs
  /-- The pool's balance just before the spec transaction. -/
  poolBefore : ℕ
  /-- The spec state just after the spec transaction. -/
  stateAfter : Spec.State
  /-- The pool's balance just after the spec transaction. -/
  poolAfter : ℕ
  /-- All admin changes before the spec transaction, in order. -/
  adminChangesBefore : List Spec.AdminChange

/-- `codeRunTxRecords d rent steps` (Code Model → spec): collects the record of each accepted
    `transact` instruction of the code run `steps`, in order. For the `transact` instruction of step `i`: its spec
    transaction (`toInputs`), the pool's balance in the state before it, the spec state and pool
    balance in the state after it, and the admin changes of the `i` steps before it
    (`adminChanges`). -/
def codeRunTxRecords (d : CodeModel.Deployment) (rent : Nat → U64) (steps : List RunStep) :
    List TxRecord :=
  steps.zipIdx.flatMap fun (step, i) =>
    match step.event with
    | .program txEnv (.transact a proof ext fee out1 out2) _ =>
      [{ inputs := toInputs ⟨txEnv.toTxContext, a, ⟨proof, ext, fee, out1, out2⟩⟩
         poolBefore := step.before.lamports d.poolAddress
         stateAfter := (toWorld d rent step.after).state
         poolAfter := step.after.lamports d.poolAddress
         adminChangesBefore := adminChanges d (steps.take i) }]
    | _ => []

section
variable [Spec.PoseidonHashes] [Spec.Sha] [Spec.Groups] [AddCommGroup Spec.G1]
  [Module Spec.F Spec.G1]
  [CommGroup Spec.GT] [Spec.Pairing] [Spec.Deployment]

/-- `runTxRecords r pool`: collects the record of each spec transaction of the spec run `r`, in
    order. For spec transaction `j`: the spec transaction, the balance of `pool` after the change
    between spec transactions before it, the state and pool balance of world `j+1`, and the admin
    changes up to it. -/
def runTxRecords {w₀ : Spec.World} (r : Spec.Run w₀) (pool : Spec.Pubkey) :
    List TxRecord :=
  r.txs.mapIdx fun j tx =>
    { inputs := tx
      poolBefore := (r.updatedValues j).balances pool
      stateAfter := (r.ws (j+1)).state
      poolAfter := (r.ws (j+1)).poolBalance
      adminChangesBefore := r.adminChangesUpTo (j+1) }

/-- `IsRunOf d rent steps sₙ params r`: the spec run `r` from `initWorld params` describes the
    code run `steps` ending in `sₙ`: same deployment, same start, same spec transactions, same
    end. -/
structure IsRunOf (d : CodeModel.Deployment) (rent : Nat → U64) (steps : List RunStep)
    (sₙ : CodeModel.State) (params : Spec.InitParams)
    (r : Spec.Run (Spec.initWorld params)) : Prop where
  /-- The deployment: `params` names this deployment's addresses, rents and admin key. -/
  deployment : RunOfDeployment d rent params
  /-- The start: `r` starts from what the code run's `initialize` (`initStep`) set up, and no
      other step of the code run is an `initialize`. The spec has one start (`initWorld`) and no
      way to initialize again. -/
  start : ∃ earlier initStep later txEnv a, steps = earlier ++ initStep :: later ∧
    initStep.IsInitialize txEnv a ∧ StartsFromInit params txEnv a (toWorld d rent initStep.after) ∧
    ∀ step ∈ earlier ++ later, ∀ txEnv' a', ¬ step.IsInitialize txEnv' a'
  /-- The spec transactions: one by one, `r`'s spec transactions are those of the code run's
      accepted `transact` instructions, with the chain's pool balance before, spec state and pool
      balance after, and admin changes
      before. So `r.donated` is what the pool received from outside. -/
  transactions :
    runTxRecords r (toPubkey d.poolAddress) = codeRunTxRecords d rent steps
  /-- The end: `sₙ` is `r`'s final world after an allowed change, which records the admin
      instructions since the last spec transaction. -/
  final : ∃ b : Spec.UpdatedValuesBetweenTransacts, b.Allowed r.final ∧
    r.adminChangesUpTo r.txs.length ++ b.adminChanges = adminChanges d steps ∧
    toWorld d rent sₙ = r.final.withUpdatedValues b

/-- `IsSpecRun d rent steps sₙ`: some spec run describes the code run `steps` ending in `sₙ`
    (`IsRunOf`). -/
def IsSpecRun (d : CodeModel.Deployment) (rent : Nat → U64) (steps : List RunStep)
    (sₙ : CodeModel.State) : Prop :=
  ∃ (params : Spec.InitParams) (r : Spec.Run (Spec.initWorld params)),
    IsRunOf d rent steps sₙ params r

end

/-! ## The verifier: the spec instantiated by the syscalls and the program's key

For the verifier bridge: the spec's groups, decoding and pairing come from the syscall
contracts `C` (core-model's `AltBn128Contracts`), its key from the program's `VERIFYING_KEY`. -/

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module Spec.F G1] [Inhabited G2]
  [CommGroup GT] {s : CodeModel.AltBn128}
open PrivacyCash.Proofs.Groth16 (ic)

/-- `syscallGroups C` (Code Model → spec): instantiates the spec's groups with the syscalls' `G1`, `G2`, `GT`,
    decoding a G1 point from 64 bytes with `C.decodeG1` and a G2 point from 128 bytes with
    `C.decodeG2`; bytes of another length decode to no point. -/
@[reducible] def syscallGroups (C : CodeModel.AltBn128Contracts s G1 G2 GT) : Spec.Groups :=
  ⟨G1, G2, GT, fun bs => (toArray 64#usize bs).bind C.decodeG1,
    fun bs => (toArray 128#usize bs).bind C.decodeG2⟩

/-- `syscallPairing C` (Code Model → spec): instantiates the spec's pairing with the syscall's
    pairing `C.e`. -/
@[reducible] def syscallPairing (C : CodeModel.AltBn128Contracts s G1 G2 GT) :
    @Spec.Pairing (syscallGroups C) :=
  @Spec.Pairing.mk (syscallGroups C) C.e

/-- `programKey C` (Code Model → spec): decodes the program's constant `VERIFYING_KEY` with the
    syscalls into the spec's verification key. A point that does not decode becomes the default
    point, which never applies: whenever the verifier accepts, every key point decodes
    (`programVerifier_groth16`). -/
@[reducible] def programKey (C : CodeModel.AltBn128Contracts s G1 G2 GT) :
    @Spec.Groth16.VerificationKey (syscallGroups C) :=
  letI : Spec.Groups := syscallGroups C
  let vk := CodeModel.VERIFYING_KEY
  { α := (C.decodeG1 vk.vk_alpha_g1).getD 0, β := (C.decodeG2 vk.vk_beta_g2).getD default,
    γ := (C.decodeG2 vk.vk_gamme_g2).getD default, δ := (C.decodeG2 vk.vk_delta_g2).getD default,
    IC := fun i => ic C vk i.val }

/-- `programDeployment C` (Code Model → spec): instantiates the spec's deployment with the program's key
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

/-- `r.txs`: the spec transactions of the spec run `r`, in order. -/
abbrev SpecRun.txs {C : CodeModel.AltBn128Contracts s G1 G2 GT}
    [Spec.PoseidonHashes] [Spec.Sha] {params : Spec.InitParams} (r : SpecRun C params) : List Spec.TxInputs :=
  withSyscallSpec C in
  Spec.Run.txs r

end

end Connection
