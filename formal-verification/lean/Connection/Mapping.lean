import PrivacyCash
import Spec.Statements
open Aeneas Aeneas.Std PrivacyCash.Model

/-! # Mapping: code-model values to spec values

REVIEW SURFACE. The connection theorems (`Connection/ConnectionTheorems.lean`) say: when the
code model accepts a `transact`, the spec's `transact` holds between the mapped worlds. Their
meaning depends on these definitions, so each is short and should be checked by reading.

A mapping that throws information away could make the theorem easier to prove but weaker.
Every map below is injective on the values that matter, except where its comment says
otherwise (field elements are read mod p; nullifier accounts are left out of the balances).
-/

namespace Connection

/-! ## Values -/

/-- `toF b`: a 32-byte public input or hash as a field element: read big-endian, reduced
    mod p (as the verifier reads public inputs; it rejects values `≥ p`). -/
def toF (b : Std.Array U8 32#usize) : LeanSpec.F := (beNat b : LeanSpec.F)

/-- `Canonical b`: the big-endian value of `b` is below the field modulus, so `toF` loses
    nothing. -/
def Canonical (b : Std.Array U8 32#usize) : Prop := beNat b < bn254ScalarModulus

/-- `toBytes l`: code bytes as the spec's bytes. -/
def toBytes (l : List U8) : LeanSpec.Bytes := l.map (·.bv)

/-- `toSlice bs`: the spec's bytes as a code byte slice (empty if too long for a slice,
    which no real transaction is). Used to say which bytes the code hashes. -/
def toSlice (bs : LeanSpec.Bytes) : Slice U8 :=
  let l : List U8 := bs.map (fun b => ⟨b⟩)
  if h : l.length ≤ Usize.max then Slice.from l h else Slice.from [] (by simp)

/-- `toPubkey k`: a Solana address as the spec's `Pubkey`, read little-endian, so that the
    spec's serialization `PubkeyToBytes` gives back the address's own 32 bytes. -/
def toPubkey (k : Pubkey) : LeanSpec.Pubkey := BitVec.ofNat 256 (leNatOfList k.val)

/-- `fromPubkey x`: the inverse of `toPubkey`. -/
def fromPubkey (x : LeanSpec.Pubkey) : Pubkey :=
  Std.Array.from (leBytes32 x.toNat) (by simp [leBytes32])

/-! ## The program's accounts -/

/-- `treeAddr d`: the canonical address of the SOL tree. -/
def treeAddr (d : Deployment) : Pubkey := d.pda merkleTreeSeeds
/-- `poolAddr d`: the canonical address of the pool. -/
def poolAddr (d : Deployment) : Pubkey := d.pda treeTokenSeeds
/-- `configAddr d`: the canonical address of the config. -/
def configAddr (d : Deployment) : Pubkey := d.pda globalConfigSeeds

/-- `treeAt s k`: the tree stored at `k` (all zeros if there is none; `WellFormed` rules
    that out). -/
def treeAt (s : State) (k : Pubkey) : zkcash_core.merkle_tree.MerkleTreeAccount :=
  match (s k).data with
  | .treeAccount t => t
  | _ => zeroTree

/-- `configAt s k`: the config stored at `k` (all zeros if there is none). -/
def configAt (s : State) (k : Pubkey) : zkcash_core.admin.GlobalConfig :=
  match (s k).data with
  | .globalConfig c => c
  | _ => ⟨Std.Array.repeat 32#usize 0#u8, 0#u16, 0#u16, 0#u16, 0#u8⟩

/-- `TreeShape t`: the tree account fields `initialize` sets and no instruction changes:
    height 26, a history of 100 roots, and a current root index inside it. -/
def TreeShape (t : zkcash_core.merkle_tree.MerkleTreeAccount) : Prop :=
  t.height.val = 26 ∧ t.root_history_size.val = 100 ∧ t.root_index.val < 100

/-- `toTree t`: the tree account as the spec's tree, field by field. `rootIndex` is reduced
    mod 100; `WellFormed` says it is already below 100. -/
def toTree (t : zkcash_core.merkle_tree.MerkleTreeAccount) : LeanSpec.Tree where
  nextIndex := t.next_index.val
  subtrees i := toF (t.subtrees.val[i.val]!)
  root := toF t.root
  history i := toF (t.root_history.val[i.val]!)
  rootIndex := ⟨t.root_index.val % 100, Nat.mod_lt _ (by decide)⟩

/-- `toConfig c t`: the config as the spec's config, field by field. The deposit limit and
    its authority live on the tree account `t` in the code. -/
def toConfig (c : zkcash_core.admin.GlobalConfig)
    (t : zkcash_core.merkle_tree.MerkleTreeAccount) : LeanSpec.config where
  authority := toPubkey c.authority
  limitAuthority := toPubkey t.authority
  depositFeeRate := c.deposit_fee_rate.val
  withdrawalFeeRate := c.withdrawal_fee_rate.val
  feeErrorMargin := c.fee_error_margin.val
  maxDepositLimit := t.max_deposit_amount.val

/-! ## Worlds -/

/-- `publicBalance s k`: the balance the spec sees for account `k`: its lamports, except
    that nullifier accounts count as 0. MAPPING DECISION: the spec's balances are those of public accounts, and the
    signer's nullifier rent leaves them (spec `nullifierRentEffects`). On-chain that rent goes to the two new nullifier accounts. -/
def publicBalance (s : State) (k : Pubkey) : ℕ :=
  match (s k).data with
  | .nullifier _ => 0
  | _ => (s k).lamports.val

/-- `toWorld d rent spent s`: the spec world the chain state `s` stands for.
    - **`rent`:** Solana's rent-exempt minimum for an account of a given size. The spec fixes
      the two amounts it uses; `OutsideSpecDetail.rentFixed` says each transaction sees this.
    - **`spent`:** the spent nullifiers, tracked alongside the chain. On-chain a nullifier is
      spent when its nullifier account exists; `WellFormed.spentRecorded` links the two. -/
def toWorld (d : Deployment) (rent : Nat → U64) (spent : Finset LeanSpec.F) (s : State) :
    LeanSpec.World where
  state :=
    { tree := toTree (treeAt s (treeAddr d))
      nullifiers := spent
      pool := toPubkey (poolAddr d)
      config := toConfig (configAt s (configAddr d)) (treeAt s (treeAddr d)) }
  balances x := publicBalance s (fromPubkey x)
  rentExemptMin := (rent treeTokenAccountSpace).val
  nullifierRent := (rent nullifierAccountSpace).val

/-! ## Transactions -/

/-- `toInputs signers a proof extAmount fee out1 out2`: the spec inputs of a `transact`
    instruction in a transaction signed by `signers`.
    The seven public inputs are given twice, as the spec's field elements (`toF`) and as the
    sender's 32 bytes (`pubInputBytes`, in circuit order); the proof is the sender's bytes of
    its three points. -/
def toInputs (signers : List Pubkey) (a : TransactAccounts) (proof : zkcash_core.transact.Proof) (extAmount : I64)
    (fee : U64) (out1 out2 : Slice U8) : LeanSpec.TxInputs where
  R := toF proof.root
  pubAmt := toF proof.public_amount
  extDataHash := toF proof.ext_data_hash
  k0 := toF proof.input_nullifiers.val[0]!
  k1 := toF proof.input_nullifiers.val[1]!
  outC0 := toF proof.output_commitments.val[0]!
  outC1 := toF proof.output_commitments.val[1]!
  extAmt := extAmount.val
  f := fee.val
  s := toPubkey a.signer
  signers := signers.map toPubkey
  A := toPubkey a.recipient
  t := toPubkey a.feeRecipientAccount
  encOut0 := toBytes out1.val
  encOut1 := toBytes out2.val
  π := ⟨toBytes proof.proof_a.val, toBytes proof.proof_b.val, toBytes proof.proof_c.val⟩
  mintAddr := toPubkey zkcash_core.transact.SOL_ADDRESS
  pubInputBytes i := toBytes ((publicInputs proof)[i.val]!).val

/-! ## Executions -/

/-- `stepTxs tx ix`: the spec transactions of one instruction in transaction `tx`: a `transact`'s
    mapped inputs; nothing for the other instructions (they are changes between transactions in
    the spec). -/
def stepTxs (tx : TxEnv) : Instruction → List LeanSpec.TxInputs
  | .transact a proof ext fee out1 out2 => [toInputs tx.signers a proof ext fee out1 out2]
  | _ => []

/-- `runTxs evs`: the spec transactions of an execution, in order. -/
def runTxs : List Event → List LeanSpec.TxInputs
  | [] => []
  | .program tx ix _ :: es => stepTxs tx ix ++ runTxs es
  | .env :: es => runTxs es

/-- The nullifiers one instruction spends (only `transact` spends any). -/
def stepSpent : Instruction → Finset LeanSpec.F
  | .transact _ proof _ _ _ _ => {toF proof.input_nullifiers.val[0]!, toF proof.input_nullifiers.val[1]!}
  | _ => ∅

/-- The nullifiers an execution spends: those of its `transact` instructions. -/
def runSpent : List Event → Finset LeanSpec.F
  | [] => ∅
  | .program _ ix _ :: es => stepSpent ix ∪ runSpent es
  | .env :: es => runSpent es

/-- `ExecutionPath d s evs states s'`: the execution `evs` from `s` to `s'`, with the state after
    each event (`states`). Core-model's `Run` with the states recorded: `Run` is a `Prop` and so
    can't tell a theorem which states it went through. The steps and their premises are `Run`'s
    (`execution_path_iff_run`, `ConnectionTheorems.lean`). -/
inductive ExecutionPath (d : Deployment) : State → List Event → List State → State → Prop where
  | nil (s : State) : ExecutionPath d s [] [] s
  | program {s s' s'' : State} {tx : TxEnv} {ix : Instruction} {emitted : List CommitmentData}
      {events : List Event} {states : List State} :
      step d s tx ix = .ok (s', emitted) → tx.RentPositive → ExecutionPath d s' events states s'' →
        ExecutionPath d s (.program tx ix emitted :: events) (s' :: states) s''
  | env {s s' s'' : State} {events : List Event} {states : List State} :
      EnvStep d.programId s s' → ExecutionPath d s' events states s'' →
        ExecutionPath d s (.env :: events) (s' :: states) s''

/-- `toAdminChange d before tx ix`: the spec's admin change for instruction `ix`, in a transaction
    `tx` run on state `before`, with the signers of `tx`. A setting `update_global_config` isn't
    given keeps its value in `before`. `none` for the other instructions. -/
def toAdminChange (d : Deployment) (before : State) (tx : TxEnv) :
    Instruction → Option LeanSpec.AdminChange
  | .updateDepositLimit _ newLimit =>
    some ⟨tx.signers.map toPubkey, .depositLimit newLimit.val⟩
  | .updateGlobalConfig _ dep wd margin =>
    let c := configAt before (configAddr d)
    some ⟨tx.signers.map toPubkey, .feeSettings (dep.getD c.deposit_fee_rate).val
      (wd.getD c.withdrawal_fee_rate).val (margin.getD c.fee_error_margin).val⟩
  | _ => none

/-- What `initialize` set up: its signing authority, the signers of its transaction, and the
    spec world of the state it left. -/
structure InitRecord where
  initializer : LeanSpec.Pubkey
  signers : List LeanSpec.Pubkey
  world : LeanSpec.World

/-- What the spec sees of an execution so far.

    - `init`: what `initialize` set up, once it has run;
    - `closedGaps`: for each transaction so far, the admin changes since the one before it;
    - `openGap`: the admin changes since the last transaction;
    - `poolBeforeTx`: just before each transaction so far, the chain's pool balance;
    - `afterTx`: after each transaction so far, the chain's spec state and pool balance;
    - `spent`: the nullifiers spent so far. -/
structure ExecutionView where
  init : Option InitRecord := none
  closedGaps : List (List LeanSpec.AdminChange) := []
  openGap : List LeanSpec.AdminChange := []
  poolBeforeTx : List ℕ := []
  afterTx : List (LeanSpec.State × ℕ) := []
  spent : Finset LeanSpec.F := ∅

/-- `v.afterEvent d rent before e after`: the view `v` after event `e` took the chain from
    `before` to `after`. Outside actions change nothing the view records. -/
def ExecutionView.afterEvent (v : ExecutionView) (d : Deployment) (rent : Nat → U64)
    (before : State) (e : Event) (after : State) : ExecutionView :=
  match e with
  | .env => v
  | .program tx ix _ =>
    match ix with
    | .initialize a =>
      { v with init := some ⟨toPubkey a.authority, tx.signers.map toPubkey,
          toWorld d rent v.spent after⟩ }
    | .transact .. =>
      let spent' := v.spent ∪ stepSpent ix
      { v with
        closedGaps := v.closedGaps ++ [v.openGap]
        openGap := []
        poolBeforeTx := v.poolBeforeTx ++ [publicBalance before (poolAddr d)]
        afterTx := v.afterTx ++ [((toWorld d rent spent' after).state,
          publicBalance after (poolAddr d))]
        spent := spent' }
    | _ => { v with openGap := v.openGap ++ (toAdminChange d before tx ix).toList }

/-- `v.afterEvents d rent before evs states`: the view `v` after the events `evs`, from `before`
    through `states`. -/
def ExecutionView.afterEvents (d : Deployment) (rent : Nat → U64) :
    ExecutionView → State → List Event → List State → ExecutionView
  | v, before, e :: es, after :: states =>
    ExecutionView.afterEvents d rent (v.afterEvent d rent before e after) after es states
  | v, _, _, _ => v

/-- `executionView d rent s₀ evs states`: what the spec sees of the whole execution. -/
def executionView (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event)
    (states : List State) : ExecutionView :=
  ExecutionView.afterEvents d rent {} s₀ evs states

/-- `Initialized d s`: the program holds its tree, pool and config at their canonical
    addresses. -/
def Initialized (d : Deployment) (s : State) : Prop :=
  (∃ t, HoldsTree d.programId s (treeAddr d) t) ∧ (∃ p, HoldsTreeToken d.programId s (poolAddr d) p) ∧
    (∃ c, HoldsGlobalConfig d.programId s (configAddr d) c)

/-- `NoProgramAccounts d s`: no account is the program's tree, pool or config. -/
def NoProgramAccounts (d : Deployment) (s : State) : Prop :=
  (∀ k t, ¬ HoldsTree d.programId s k t) ∧ (∀ k p, ¬ HoldsTreeToken d.programId s k p) ∧
    ∀ k c, ¬ HoldsGlobalConfig d.programId s k c

section
variable [LeanSpec.PoseidonHashes] [LeanSpec.Sha] [LeanSpec.Groups] [AddCommGroup LeanSpec.G1]
  [Module LeanSpec.F LeanSpec.G1] [AddCommGroup LeanSpec.G2] [Module LeanSpec.F LeanSpec.G2]
  [CommGroup LeanSpec.GT] [LeanSpec.Pairing] [LeanSpec.Deployment]

/-- `RunMatchesView d rent v spent txs s params r`: the spec run `r` is what the view `v` records,
    and it ends at the code state `s`. The conditions are explained at `IsRunOf`, which applies this
    to a whole execution. -/
def RunMatchesView (d : Deployment) (rent : Nat → U64) (v : ExecutionView) (spent : Finset LeanSpec.F)
    (txs : List LeanSpec.TxInputs) (s : State) (params : LeanSpec.InitParams)
    (r : LeanSpec.Run (LeanSpec.initWorld params)) : Prop :=
  -- the start
  params.pool = toPubkey (poolAddr d) ∧ params.rentExemptMin = (rent treeTokenAccountSpace).val ∧
    params.nullifierRent = (rent nullifierAccountSpace).val ∧
    params.admin = d.adminPubkey.map toPubkey ∧
    (∃ i : InitRecord, v.init = some i ∧ params.initializer = i.initializer ∧
      params.signers = i.signers ∧ params.cfg = i.world.state.config ∧
      params.balances = i.world.balances) ∧
    -- the transactions
    r.txs = txs ∧
    -- the pool's balance before each transaction, so the donations are the chain's
    v.poolBeforeTx.length = r.txs.length ∧
    (∀ j (_ : j < r.txs.length),
      v.poolBeforeTx[j]? = some ((r.updatedValues j).balances (toPubkey (poolAddr d)))) ∧
    -- each transaction's result
    v.afterTx.length = r.txs.length ∧
    (∀ j (_ : j < r.txs.length), v.afterTx[j]? = some ((r.ws (j+1)).state, (r.ws (j+1)).poolBalance)) ∧
    -- the admin changes
    v.closedGaps.length = r.txs.length ∧
    (∀ j (_ : j < r.txs.length), v.closedGaps[j]? = some (r.updatedValues j).adminChanges) ∧
    -- the end
    ∃ b : LeanSpec.UpdatedValuesBetweenTransacts, b.Allowed r.final ∧
      b.adminChanges = v.openGap ∧ toWorld d rent spent s = r.final.withUpdatedValues b

/-- `IsRunOf d rent s₀ evs states s params r`: `r` is the spec run of this execution: the one
    `evs` went through, from `s₀` to `s`, by the `states` of its `ExecutionPath`.

    - **the start:** `r` starts at the world `initialize` set up (`view.init`): its config and
      balances, its signing authority and the signers of its transaction; and `params` holds the
      deployment's pool address, rents and admin key;
    - **the transactions:** its transactions are the execution's (`runTxs evs`);
    - **the pool before each transaction:** `r` has the chain's pool balance, so the SOL `r` counts
      as sent to the pool (`r.donated`) is what the chain received;
    - **each transaction's result:** after each transaction, `r` has the chain's tree, nullifiers,
      pool address, config and pool balance. Other balances may differ (see
      `OutsideSpecDetail`: a pre-funded nullifier address, or a payee that is a nullifier account);
    - **the admin changes:** before each transaction, `r` records exactly the admin instructions
      executed since the last one, with the signers of their transactions;
    - **the end:** the code state `s`, with the nullifiers the execution spent, is its final world
      after an allowed change that records the admin instructions executed since the last
      transaction. -/
def IsRunOf (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event)
    (states : List State) (s : State) (params : LeanSpec.InitParams)
    (r : LeanSpec.Run (LeanSpec.initWorld params)) : Prop :=
  RunMatchesView d rent (executionView d rent s₀ evs states) (runSpent evs) (runTxs evs) s params r

/-- `IsSpecRun d rent s₀ evs states s`: the execution is a spec run (some `r` with `IsRunOf`). -/
def IsSpecRun (d : Deployment) (rent : Nat → U64) (s₀ : State) (evs : List Event)
    (states : List State) (s : State) : Prop :=
  ∃ (params : LeanSpec.InitParams) (r : LeanSpec.Run (LeanSpec.initWorld params)),
    IsRunOf d rent s₀ evs states s params r

end

/-! ## The handler's view (for handler completeness)

The extracted `transact` handler runs after Anchor's account checks and `init`s, on the
runtime environment `execTransact` builds. Handler completeness compares it with the spec
`transact` from the world the handler sees. -/

/-- `handlerEnv a s₁ v`: the runtime environment the handler runs in, exactly as
    `execTransact` builds it: the state `s₁` after Anchor's two `init`s, the instruction's
    accounts, the rent-exempt minimum `v`. -/
def handlerEnv (a : TransactAccounts) (s₁ : State) (v : U64) : SolEnv :=
  { accounts := s₁, balances := s₁.balances, signer := a.signer,
    treeToken := a.treeTokenAccount, recipient := a.recipient,
    feeRecipient := a.feeRecipientAccount, rentExemptMinimum := some v }

/-- `handlerWorld a s₁ v tree config spent`: the spec world the handler sees (used only by
    handler completeness): every account's lamports in `s₁`, the tree and config it is
    given, the pool's address, the rent-exempt minimum `v`, and the nullifiers `spent` (the
    handler does not read them).

    MAPPING DECISION: `nullifierRent := 0`, because Anchor has already paid the two
    nullifier accounts' rent before the handler runs; the handler's effects are the spec's
    transfer and fee effects.

    How it differs from `toWorld` (the connection theorems' world):
    - **when:** after Anchor's two `init`s, not before;
    - **balances:** every account's raw lamports, nullifier accounts included (`toWorld`
      counts those as 0, `publicBalance`), since the handler never pays them in the cases it
      covers;
    - **rent:** the handler's own `v`. -/
def handlerWorld (a : TransactAccounts) (s₁ : State) (v : U64)
    (tree : zkcash_core.merkle_tree.MerkleTreeAccount) (config : zkcash_core.admin.GlobalConfig)
    (spent : Finset LeanSpec.F) : LeanSpec.World where
  state :=
    { tree := toTree tree
      nullifiers := spent
      pool := toPubkey a.treeTokenAccount
      config := toConfig config tree }
  balances x := (s₁ (fromPubkey x)).lamports.val
  rentExemptMin := v.val
  nullifierRent := 0

/-! ## The verifier: the spec instantiated by the syscalls and the program's key

The spec's groups, point decoding, pairing and deployed key, for the verifier bridge. The
groups `G1 G2 GT` and the point decoding come from the syscall contracts `C` (core-model's
`AltBn128Contracts`); the key is the program's extracted `VERIFYING_KEY`. -/

/-- `toArray n bs`: the spec's bytes as an `n`-byte code array, if there are exactly `n`. -/
def toArray (n : Usize) (bs : LeanSpec.Bytes) : Option (Std.Array U8 n) :=
  if h : bs.length = n.val then
    some (Std.Array.from (bs.map (fun b => (⟨b⟩ : U8))) (by simp [h]))
  else none

section
variable {G1 G2 GT : Type} [AddCommGroup G1] [Module LeanSpec.F G1] [AddCommGroup G2]
  [Module LeanSpec.F G2] [CommGroup GT] {s : AltBn128}
open PrivacyCash.Proofs.Groth16 (ic)

/-- `syscallGroups C`: the spec's groups and point decoding are the syscalls'. A G1 point is
    64 bytes and a G2 point 128 bytes, decoded as the syscalls decode them (`C.decodeG1`,
    `C.decodeG2`); bytes of any other length are not a point. -/
@[reducible] def syscallGroups (C : AltBn128Contracts s G1 G2 GT) : LeanSpec.Groups :=
  ⟨G1, G2, GT, fun bs => (toArray 64#usize bs).bind C.decodeG1,
    fun bs => (toArray 128#usize bs).bind C.decodeG2⟩

/-- `syscallPairing C`: the spec's pairing is the syscall's. -/
@[reducible] def syscallPairing (C : AltBn128Contracts s G1 G2 GT) :
    @LeanSpec.Pairing (syscallGroups C) :=
  @LeanSpec.Pairing.mk (syscallGroups C) C.e

/-- `programKey C`: the spec's deployed key is the program's key, as the syscalls decode it. The key is the
    program's own constant, not sender data; whenever the verifier accepts a proof, every one
    of its points decodes (`programVerifier_groth16`), so the default `0` is never used. -/
@[reducible] def programKey (C : AltBn128Contracts s G1 G2 GT) :
    @LeanSpec.Groth16.VerificationKey (syscallGroups C) :=
  letI : LeanSpec.Groups := syscallGroups C
  let vk := zkcash_core.verifying_key.VERIFYING_KEY
  { α := (C.decodeG1 vk.vk_alpha_g1).getD 0, β := (C.decodeG2 vk.vk_beta_g2).getD 0,
    γ := (C.decodeG2 vk.vk_gamme_g2).getD 0, δ := (C.decodeG2 vk.vk_delta_g2).getD 0,
    IC := fun i => ic C vk i.val }

end

/-! ## Decidability (so a statement can say the code returns `decide (spec predicate)`) -/

/-- `p_eq`: the spec's field and the code's field are the same, `ZMod p` with the same `p`. -/
theorem p_eq : LeanSpec.p = bn254ScalarModulus := rfl

instance (extAmt : ℤ) (f : ℕ) (pubAmt : LeanSpec.F) :
    Decidable (LeanSpec.pubAmtConsistent extAmt f pubAmt) := by
  unfold LeanSpec.pubAmtConsistent; infer_instance

instance (extAmt : ℤ) (f : ℕ) : Decidable (LeanSpec.amountsInRange extAmt f) := by
  unfold LeanSpec.amountsInRange; infer_instance

instance (inputs : LeanSpec.TxInputs) : Decidable (LeanSpec.encOutsFit inputs) := by
  unfold LeanSpec.encOutsFit; infer_instance

instance (T : LeanSpec.Tree) (R : LeanSpec.F) : Decidable (LeanSpec.rootKnown T R) :=
  decidable_of_iff ((∃ i, T.history i = R) ∧ R ≠ 0) (by simp [LeanSpec.rootKnown, Set.mem_range])

instance (T : LeanSpec.Tree) (bs : LeanSpec.Bytes) : Decidable (LeanSpec.rootBytesKnown T bs) := by
  unfold LeanSpec.rootBytesKnown; infer_instance

end Connection
