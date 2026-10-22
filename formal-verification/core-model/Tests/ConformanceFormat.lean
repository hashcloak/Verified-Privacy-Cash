/-
The vocabulary the conformance traces are written in (`Tests/ConformanceTraces.lean`):
hex bytes, accounts, the scenario format. Hand-written; `Tests/Conformance.lean`
explains the check.
-/
import PrivacyCash
open Aeneas Aeneas.Std PrivacyCash.Model

namespace PrivacyCash.Tests.Conformance

/-! ## Reading the trace -/

/-- A hex digit's value (anything else reads as 0; the traces only contain hex). -/
def hexDigit (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then c.toNat - '0'.toNat
  else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 'a'.toNat + 10 else 0

/-- A byte as the model's `U8`. -/
def byte (n : Nat) : U8 := U8.ofNatCore (n % 256) (by simp only [UScalarTy.numBits]; omega)

/-- Bytes written as hex. -/
def bytes (s : String) : List U8 :=
  let ds := s.toList.map hexDigit
  (List.range (ds.length / 2)).map fun i => byte (16 * ds[2 * i]! + ds[2 * i + 1]!)

/-- A fixed-size array from a list; a list of the wrong length gives an array of
    `fill` (which then fails the comparison, so a malformed trace cannot pass). -/
def arrayOf {α : Type} {n : Usize} (fill : α) (l : List α) : Std.Array α n :=
  if h : l.length = n.val then Std.Array.from l h else Std.Array.repeat n fill

def b32 (s : String) : Std.Array U8 32#usize := arrayOf (byte 255) (bytes s)
def pk (s : String) : Pubkey := b32 s
def u64 (n : Nat) : U64 := ⟨BitVec.ofNat 64 n⟩
def u16 (n : Nat) : U16 := ⟨BitVec.ofNat 16 n⟩
def ou16 (n : Option Nat) : Option U16 := n.map u16

def acct (lamports : Nat) (owner : Pubkey) (data : AccountData) : Account :=
  { lamports := u64 lamports, owner, data }

/-- Entries written as runs of equal entries: `(entry, count)`. -/
def rle (runs : List (String × Nat)) : List String := runs.flatMap fun (h, n) => List.replicate n h

def tree (authority : Pubkey) (nextIndex : Nat) (subtrees : List String) (root : String)
    (rootHistory : List String) (rootIndex maxDeposit height rootHistorySize bump : Nat)
    (padding : String) : zkcash_core.merkle_tree.MerkleTreeAccount where
  authority := authority
  next_index := u64 nextIndex
  subtrees := arrayOf (b32 "") (subtrees.map b32)
  root := b32 root
  root_history := arrayOf (b32 "") (rootHistory.map b32)
  root_index := u64 rootIndex
  max_deposit_amount := u64 maxDeposit
  height := byte height
  root_history_size := byte rootHistorySize
  bump := byte bump
  _padding := arrayOf (byte 255) (bytes padding)

def treeToken (authority : Pubkey) (bump : Nat) : zkcash_core.admin.TreeTokenAccount :=
  ⟨authority, byte bump⟩

def globalConfig (authority : Pubkey) (deposit withdrawal margin bump : Nat) :
    zkcash_core.admin.GlobalConfig :=
  ⟨authority, u16 deposit, u16 withdrawal, u16 margin, byte bump⟩

/-- What the program did. -/
inductive Expected where
  /-- It succeeded: the accounts after, and the events emitted. -/
  | ok (post : List (Pubkey × Account)) (events : List CommitmentData)
  /-- Anchor rejected an account (its log line, for the reader). -/
  | accounts (log : String)
  /-- The handler returned this program error code. -/
  | program (code : Nat)
  /-- The system program failed (inside Anchor's `init`, or a transfer). -/
  | system (code : Nat)
  /-- Another Anchor framework error (none of the model's failures). -/
  | anchor (code : Nat) (log : String)
  /-- The runtime rejected the instruction. -/
  | runtime (error : String)

/-- The crypto answers of a `transact` scenario, as (input, output) in hex:
    every Poseidon, SHA-256 and `alt_bn128` call the program's code makes on
    it (recorded by the harness running the extracted `transact` on the host
    with the program's primitives; `none` is a failed call). -/
structure Tables where
  poseidon : List (String × String × String) := []
  sha : List (String × String) := []
  multiplication : List (String × Option String) := []
  addition : List (String × Option String) := []
  pairing : List (String × Option String) := []

structure Scenario where
  title : String
  pre : List (Pubkey × Account)
  signers : List Pubkey
  ix : Instruction
  expected : Expected
  crypto : Tables := {}

def i64 (n : Int) : I64 := ⟨BitVec.ofInt 64 n⟩

def slice (s : String) : Slice U8 :=
  let l := bytes s
  if h : l.length ≤ Usize.max then Slice.from l h else Slice.from [] (by simp)

def proofOf (a b c root publicAmount extDataHash n0 n1 c0 c1 : String) : zkcash_core.transact.Proof where
  proof_a := arrayOf (byte 255) (bytes a)
  proof_b := arrayOf (byte 255) (bytes b)
  proof_c := arrayOf (byte 255) (bytes c)
  root := b32 root
  public_amount := b32 publicAmount
  ext_data_hash := b32 extDataHash
  input_nullifiers := arrayOf (b32 "") [b32 n0, b32 n1]
  output_commitments := arrayOf (b32 "") [b32 c0, b32 c1]

end PrivacyCash.Tests.Conformance
