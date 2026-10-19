import Connection.TransactSafety
open Aeneas Aeneas.Std Result
open LeanSpec (F)

/-! # Code-reachable states map to spec-reachable worlds

`transactSafe` is one step. This file closes the loop:

* `codeInitState`: the state `initialize` leaves behind (hand-modelled, see below).
* `CodeStep`: one successful `fv_transact_entry` call, plus the facts about the world
  outside the code model that each call relies on.
* `initRefines`: the initial code state maps to the spec's `initWorld`.
* `reachableRefines`: every state reachable from it by `CodeStep`s maps to a world
  reachable from `initWorld` by `transact` steps.

Every spec invariant of the form `ReachableWorld (initWorld …) w → P w` then holds of the
mapped code state (see `codeInvariant` at the end).

## What a code state is

The code model only sees the tree account, the global config and the pool's lamports.
The spec's `World` also has every account's balance and the spent-nullifier set, which on
Solana live in accounts `fv_transact_entry` never returns. `SysState` carries them as
ghost state, and `CodeStep` says how a call changes them: the three accounts the call
touches take the lamports the code returns, and the two input nullifiers become spent
(the Anchor PDA `init` the real instruction performs). -/

/-- The on-chain state the connection tracks: what the code model sees (`tree`, `config`,
`pool`), the rent-exempt minimum, and the ghost state the code can't see. -/
structure SysState where
  tree : zkcash.MerkleTreeAccount
  config : zkcash.GlobalConfig
  pool : Std.U64
  rent : Std.U64
  balances : LeanSpec.Pubkey → ℕ
  nullifiers : Finset F

/-- The spec world a `SysState` stands for (the same mapping `transactSafe` uses). -/
def SysState.toWorld (σ : SysState) : LeanSpec.World :=
  mapOldWorld σ.tree σ.config σ.nullifiers σ.balances σ.pool σ.rent

/-! ## The initial state

TRANSCRIBED, not extracted: `initialize` (`lib.rs:72`) and `MerkleTree::initialize`
(`merkle_tree.rs:9`) are not in the code model yet (MODEL_COVERAGE.md). Field by field:

* tree account (`load_init`, so every byte starts at 0): `next_index = 0`, `root_index = 0`,
  `max_deposit_amount = 1_000_000_000_000`, `height = MERKLE_TREE_HEIGHT = 26`,
  `root_history_size = 100`; then `subtrees[i] = zero_bytes[i]` for `i < 26`,
  `root = root_history[0] = zero_bytes[26]`, the other 99 history slots stay all-zero.
* global config: `deposit_fee_rate = 0`, `withdrawal_fee_rate = 25`, `fee_error_margin = 500`.
* pool: Anchor `init` funds the tree token account with exactly its rent-exempt minimum.

`zb` is whatever the `zero_bytes` axiom returns; `authority`/bumps are free. Replace this
with the extracted `initialize` once it is in the model. -/

/-- The 32-byte all-zero array (an untouched account slot). -/
def zero32 : Array Std.U8 32#usize := Array.repeat 32#usize 0#u8

def codeInitTree (authority : solana_pubkey.Pubkey) (bump : Std.U8)
    (zb : Array (Array Std.U8 32#usize) 41#usize) : zkcash.MerkleTreeAccount where
  authority := authority
  next_index := 0#u64
  subtrees := ⟨(List.finRange 26).map fun i => zb.val[i.val]!, by simp⟩
  root := zb.val[26]!
  root_history := ⟨zb.val[26]! :: List.replicate 99 zero32, by simp⟩
  root_index := 0#u64
  max_deposit_amount := 1000000000000#u64
  height := 26#u8
  root_history_size := 100#u8
  bump := bump
  _padding := Array.repeat 5#usize 0#u8

def codeInitConfig (authority : solana_pubkey.Pubkey) (bump : Std.U8) : zkcash.GlobalConfig where
  authority := authority
  deposit_fee_rate := 0#u16
  withdrawal_fee_rate := 25#u16
  fee_error_margin := 500#u16
  bump := bump

def codeInitState (authority : solana_pubkey.Pubkey) (treeBump configBump : Std.U8)
    (zb : Array (Array Std.U8 32#usize) 41#usize) (rent : Std.U64)
    (balances : LeanSpec.Pubkey → ℕ) : SysState where
  tree := codeInitTree authority treeBump zb
  config := codeInitConfig authority configBump
  pool := rent
  rent := rent
  balances := balances
  nullifiers := ∅

theorem treeExt {t1 t2 : LeanSpec.Tree} (h1 : t1.nextIndex = t2.nextIndex)
    (h2 : t1.subtrees = t2.subtrees) (h3 : t1.root = t2.root) (h4 : t1.history = t2.history)
    (h5 : t1.rootIndex = t2.rootIndex) : t1 = t2 := by
  cases t1; cases t2; simp_all

/-- **Base case.** The initial code state maps to `initWorld`, given that the `zero_bytes`
constants are the spec's zero-subtree ladder `Z` (levels `0..26`; level 26 is the empty
tree's root). -/
theorem initRefines [LeanSpec.PoseidonHashes]
    (authority : solana_pubkey.Pubkey) (treeBump configBump : Std.U8)
    (zb : Array (Array Std.U8 32#usize) 41#usize) (rent : Std.U64)
    (balances : LeanSpec.Pubkey → ℕ)
    (hZ : ∀ i : Fin 27, mapBytesToF (zb.val[i.val]!) = LeanSpec.Z i.val) :
    (codeInitState authority treeBump configBump zb rent balances).toWorld
      = LeanSpec.initWorld
          (mapGlobalConfig (codeInitConfig authority configBump) 1000000000000#u64)
          balances rent.val := by
  have hz : mapBytesToF zero32 = 0 := by simp [zero32, mapBytesToF, mapBytesToNat]
  have htree : mapTree (codeInitTree authority treeBump zb) = LeanSpec.initTree := by
    apply treeExt
    · rfl
    · funext i
      show mapBytesToF ((List.finRange 26).map fun j => zb.val[j.val]!)[i.val]! = LeanSpec.Z i.val
      rw [getElem!_pos _ _ (by simp)]
      simp only [List.getElem_map, List.getElem_finRange]
      have := hZ ⟨i.val, by omega⟩
      simpa using this
    · exact hZ 26
    · funext i
      show mapBytesToF (zb.val[26]! :: List.replicate 99 zero32)[i.val]!
        = if i = 0 then LeanSpec.Z 26 else 0
      by_cases hi : i = 0
      · subst hi; simpa using hZ 26
      · obtain ⟨k, hk⟩ : ∃ k, i.val = k + 1 := ⟨i.val - 1, by
          have : i.val ≠ 0 := fun h => hi (Fin.ext h)
          omega⟩
        have hk99 : k < 99 := by omega
        rw [if_neg hi, hk, List.getElem!_cons_succ,
          getElem!_pos _ _ (by rw [List.length_replicate]; exact hk99), List.getElem_replicate, hz]
    · rfl
  simp only [SysState.toWorld, codeInitState, mapOldWorld, LeanSpec.initWorld, htree]
  rfl

/-! ## One step: a successful `fv_transact_entry` call -/

/-- The state after a successful call: the code's returned tree and pool, the three touched
accounts' new lamports, and the two input nullifiers marked spent. Built from `mapNewWorld`
so that its `toWorld` is exactly the world `transactSafe` talks about. -/
def stepState (σ : SysState) (inputs : LeanSpec.TxInputs) (tree' : zkcash.MerkleTreeAccount)
    (pool' signer' : Std.U64) (recipient' feeRecipient' : zkcash.FvAccount) : SysState where
  tree := tree'
  config := σ.config
  pool := pool'
  rent := σ.rent
  balances := (mapNewWorld inputs σ.toWorld tree' σ.config pool' signer' recipient'
    feeRecipient').balances
  nullifiers := σ.nullifiers ∪ {inputs.k0, inputs.k1}

theorem stepState_toWorld (σ : SysState) (inputs : LeanSpec.TxInputs)
    (tree' : zkcash.MerkleTreeAccount) (pool' signer' : Std.U64)
    (recipient' feeRecipient' : zkcash.FvAccount) :
    (stepState σ inputs tree' pool' signer' recipient' feeRecipient').toWorld
      = mapNewWorld inputs σ.toWorld tree' σ.config pool' signer' recipient' feeRecipient' :=
  rfl

section
variable [LeanSpec.Sha] [LeanSpec.PoseidonHashes]
  [AddCommGroup LeanSpec.G1] [Module F LeanSpec.G1] [AddCommGroup LeanSpec.G2]
  [Module F LeanSpec.G2] [CommGroup LeanSpec.GT] [LeanSpec.Pairing] [LeanSpec.Deployment]

/-- One successful transaction from `σ`. The premises are the per-transaction facts about
the world outside the code model that `transactSafe` needs (same groups, same reasons):
the accounts handed to the code carry their real balances; recipient ≠ fee recipient; the
nullifier PDAs don't exist yet; the verifier is sound; the proof's root is canonical; the
encrypted outputs fit the serializer; and the two **code deviations** (`hDevPool`,
`hDevRoom`), i.e. the step also meets the spec's stricter conditions. -/
inductive CodeStep : SysState → SysState → Prop
  | transact (σ : SysState)
      (proof_root proof_ext_data_hash proof_public_amount : Array Std.U8 32#usize)
      (input_nullifiers output_commitments : Array (Array Std.U8 32#usize) 2#usize)
      (proof_a : Array Std.U8 64#usize) (proof_b : Array Std.U8 128#usize)
      (proof_c : Array Std.U8 64#usize) (ext_data_minified : zkcash.ExtDataMinified)
      (encrypted_output1 encrypted_output2 : alloc.vec.Vec Std.U8)
      (signer_lamports : Std.U64) (recipient fee_recipient_account : zkcash.FvAccount)
      (ext_data : zkcash.ExtData) (s : LeanSpec.Pubkey) (π : LeanSpec.Groth16.Proof)
      (tree' : zkcash.MerkleTreeAccount) (pool' signer' : Std.U64)
      (recipient' feeRecipient' : zkcash.FvAccount)
      (h : zkcash.fv_transact_entry σ.tree σ.config proof_root proof_ext_data_hash
            proof_public_amount input_nullifiers output_commitments proof_a proof_b proof_c
            ext_data_minified encrypted_output1 encrypted_output2 σ.rent σ.pool
            signer_lamports recipient fee_recipient_account
          = ok (.Ok (), tree', pool', signer', recipient', feeRecipient'))
      (hextdata : zkcash.fv_ext_data_from_minified recipient fee_recipient_account
          ext_data_minified = ok ext_data)
      (hbalS : σ.balances s = signer_lamports.val)
      (hbalA : σ.balances (mapPubkey recipient.key) = recipient.lamports.val)
      (hbalT : σ.balances (mapPubkey fee_recipient_account.key)
          = fee_recipient_account.lamports.val)
      (hAT : mapPubkey recipient.key ≠ mapPubkey fee_recipient_account.key)
      (hFresh : LeanSpec.nullifiersFresh σ.nullifiers (mapBytesToF input_nullifiers.val[0]!)
          (mapBytesToF input_nullifiers.val[1]!))
      (hVerifySound : ∀ a a1 a2 a3 a4,
          curve_shim.FV_VK_ALPHA_G1 = ok a → curve_shim.FV_VK_BETA_G2 = ok a1 →
          curve_shim.FV_VK_GAMME_G2 = ok a2 → curve_shim.FV_VK_DELTA_G2 = ok a3 →
          curve_shim.FV_VK_IC = ok a4 →
          zkcash.utils.fv_verify_proof_full_entry proof_root proof_public_amount
            proof_ext_data_hash input_nullifiers output_commitments proof_a proof_b proof_c
            a a1 a2 a3 a4 = ok true →
          LeanSpec.proofValid (mapTxInputs s π proof_root proof_ext_data_hash
            proof_public_amount input_nullifiers output_commitments ext_data
            encrypted_output1 encrypted_output2))
      (hExtDataSum : 32 + 8 + (4 + (alloc.vec.Vec.deref encrypted_output1).length)
          + (4 + (alloc.vec.Vec.deref encrypted_output2).length) + 8 + 32 + 32 ≤ Std.Usize.max)
      (hRootCanon : canonical proof_root)
      (hDevPool : ext_data.ext_amount.val > 0 → ext_data.fee.val > 0 →
          σ.pool.val ≥ ext_data.fee.val + σ.rent.val)
      (hDevRoom : σ.tree.next_index.val < 2 ^ 26 - 2) :
      CodeStep σ (stepState σ (mapTxInputs s π proof_root proof_ext_data_hash
        proof_public_amount input_nullifiers output_commitments ext_data encrypted_output1
        encrypted_output2) tree' pool' signer' recipient' feeRecipient')

/-- States reachable by any number of `CodeStep`s. -/
inductive CodeReachable : SysState → SysState → Prop
  | refl (σ : SysState) : CodeReachable σ σ
  | step {σ1 σ2 σ3 : SysState} : CodeReachable σ1 σ2 → CodeStep σ2 σ3 → CodeReachable σ1 σ3

/-- What every code-reachable state satisfies that `transactSafe` needs of its input:
a well-formed tree account and fee rates within 100%. -/
def CodeInv (σ : SysState) : Prop :=
  TreeShape σ.tree ∧ σ.config.deposit_fee_rate.val ≤ 10000 ∧
    σ.config.withdrawal_fee_rate.val ≤ 10000 ∧ σ.config.fee_error_margin.val ≤ 10000

/-- **Induction.** Every state reachable from the initial code state satisfies `CodeInv`
and maps to a world reachable from `initWorld`. The hash-agreement hypotheses are global
(the same hash functions throughout); everything per-transaction is in `CodeStep`. -/
theorem reachableRefines
    (hSha : ∀ (bytes : List Std.U8) (h : bytes.length ≤ Std.Usize.max),
      ∃ digest : Array Std.U8 32#usize,
        solana_sha256_hasher.hash ⟨bytes, h⟩ = ok digest ∧
        mapBytesToByteList digest.val = LeanSpec.Sha.sha256 (mapBytesToByteList bytes))
    (hHashv : ∀ a b : Array Std.U8 32#usize, ∃ h : Array Std.U8 32#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.hashv
          ⟨[⟨a.val, by scalar_tac⟩, ⟨b.val, by scalar_tac⟩], by scalar_tac⟩
        = ok (core.result.Result.Ok h) ∧
        mapBytesToF h = LeanSpec.PoseidonHashes.H2 (mapBytesToF a) (mapBytesToF b))
    (zb : Array (Array Std.U8 32#usize) 41#usize)
    (hzb : light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.zero_bytes = ok zb)
    (hZ : ∀ i : Fin 27, mapBytesToF (zb.val[i.val]!) = LeanSpec.Z i.val)
    (authority : solana_pubkey.Pubkey) (treeBump configBump : Std.U8) (rent : Std.U64)
    (balances : LeanSpec.Pubkey → ℕ) (σ : SysState)
    (hreach : CodeReachable (codeInitState authority treeBump configBump zb rent balances) σ) :
    CodeInv σ ∧
      LeanSpec.ReachableWorld
        (LeanSpec.initWorld
          (mapGlobalConfig (codeInitConfig authority configBump) 1000000000000#u64)
          balances rent.val)
        σ.toWorld := by
  induction hreach with
  | refl =>
    refine ⟨?_, ?_⟩
    · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> simp [codeInitState, codeInitTree, codeInitConfig]
    rw [initRefines authority treeBump configBump zb rent balances hZ]
    exact LeanSpec.ReachableWorld.noStep _
  | @step σ _ _ hstep ih =>
    obtain ⟨⟨hheight, hsize, hidx⟩, hdrate, hwrate, hmrate⟩ := ih.1
    cases hstep with
    | transact proof_root proof_ext_data_hash proof_public_amount input_nullifiers
        output_commitments proof_a proof_b proof_c ext_data_minified encrypted_output1
        encrypted_output2 signer_lamports recipient fee_recipient_account ext_data s π
        tree' pool' signer' recipient' feeRecipient' h hextdata hbalS hbalA hbalT hAT hFresh
        hVerifySound hExtDataSum hRootCanon hDevPool hDevRoom =>
      have hsafe := transactSafe σ.tree σ.config proof_root proof_ext_data_hash
        proof_public_amount input_nullifiers output_commitments proof_a proof_b proof_c
        ext_data_minified encrypted_output1 encrypted_output2 σ.rent σ.pool signer_lamports
        recipient fee_recipient_account ext_data s π σ.nullifiers σ.balances tree' pool'
        signer' recipient' feeRecipient' h hextdata hbalS hbalA hbalT hAT hFresh hVerifySound
        hSha hHashv ⟨zb, hzb, fun i => hZ ⟨i.val, by omega⟩⟩ hExtDataSum hdrate hwrate hmrate
        hRootCanon hsize hidx hheight hDevPool hDevRoom
      refine ⟨⟨hsafe.2, hdrate, hwrate, hmrate⟩, ?_⟩
      rw [stepState_toWorld]
      exact LeanSpec.ReachableWorld.extend _ ih.2 hsafe.1

/-- **Every spec invariant holds of the code.** Any property the spec proves of all worlds
reachable from `initWorld` holds of every code-reachable state (under the same
assumptions as `reachableRefines`). -/
theorem codeInvariant (P : LeanSpec.World → Prop)
    (hSha : ∀ (bytes : List Std.U8) (h : bytes.length ≤ Std.Usize.max),
      ∃ digest : Array Std.U8 32#usize,
        solana_sha256_hasher.hash ⟨bytes, h⟩ = ok digest ∧
        mapBytesToByteList digest.val = LeanSpec.Sha.sha256 (mapBytesToByteList bytes))
    (hHashv : ∀ a b : Array Std.U8 32#usize, ∃ h : Array Std.U8 32#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.hashv
          ⟨[⟨a.val, by scalar_tac⟩, ⟨b.val, by scalar_tac⟩], by scalar_tac⟩
        = ok (core.result.Result.Ok h) ∧
        mapBytesToF h = LeanSpec.PoseidonHashes.H2 (mapBytesToF a) (mapBytesToF b))
    (zb : Array (Array Std.U8 32#usize) 41#usize)
    (hzb : light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.zero_bytes = ok zb)
    (hZ : ∀ i : Fin 27, mapBytesToF (zb.val[i.val]!) = LeanSpec.Z i.val)
    (authority : solana_pubkey.Pubkey) (treeBump configBump : Std.U8) (rent : Std.U64)
    (balances : LeanSpec.Pubkey → ℕ) (σ : SysState)
    (hreach : CodeReachable (codeInitState authority treeBump configBump zb rent balances) σ)
    (hP : ∀ w, LeanSpec.ReachableWorld (LeanSpec.initWorld
        (mapGlobalConfig (codeInitConfig authority configBump) 1000000000000#u64)
        balances rent.val) w → P w) :
    P σ.toWorld :=
  hP _ (reachableRefines hSha hHashv zb hzb hZ authority treeBump configBump rent balances σ
    hreach).2

/-- Example: invariant 3 (SOL balance correctness) on the code. The pool account's lamports
equal its rent reserve plus the net `extAmt − f` of the transactions that got it there. -/
theorem codeSolBalanceCorrect
    (hSha : ∀ (bytes : List Std.U8) (h : bytes.length ≤ Std.Usize.max),
      ∃ digest : Array Std.U8 32#usize,
        solana_sha256_hasher.hash ⟨bytes, h⟩ = ok digest ∧
        mapBytesToByteList digest.val = LeanSpec.Sha.sha256 (mapBytesToByteList bytes))
    (hHashv : ∀ a b : Array Std.U8 32#usize, ∃ h : Array Std.U8 32#usize,
      light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.hashv
          ⟨[⟨a.val, by scalar_tac⟩, ⟨b.val, by scalar_tac⟩], by scalar_tac⟩
        = ok (core.result.Result.Ok h) ∧
        mapBytesToF h = LeanSpec.PoseidonHashes.H2 (mapBytesToF a) (mapBytesToF b))
    (zb : Array (Array Std.U8 32#usize) 41#usize)
    (hzb : light_hasher.poseidon.Poseidon.Insts.Light_hasherHasher.zero_bytes = ok zb)
    (hZ : ∀ i : Fin 27, mapBytesToF (zb.val[i.val]!) = LeanSpec.Z i.val)
    (authority : solana_pubkey.Pubkey) (treeBump configBump : Std.U8) (rent : Std.U64)
    (balances : LeanSpec.Pubkey → ℕ) (σ : SysState)
    (hreach : CodeReachable (codeInitState authority treeBump configBump zb rent balances) σ) :
    ∃ txs : List LeanSpec.TxInputs, (σ.pool.val : ℤ)
      = txs.foldl (fun acc (tx : LeanSpec.TxInputs) => acc + tx.extAmt - tx.f) (rent.val : ℤ) :=
  codeInvariant (fun w => ∃ txs : List LeanSpec.TxInputs, (w.state.solBalance : ℤ)
      = txs.foldl (fun acc (tx : LeanSpec.TxInputs) => acc + tx.extAmt - tx.f) (rent.val : ℤ))
    hSha hHashv zb hzb hZ authority treeBump configBump rent balances σ hreach
    (fun w hw => LeanSpec.sol_balance_correctness _ _ _ w hw)

end
