/-
The rest of the program's interface agrees with its IDL: instruction
arguments, the layout of the account data and argument types, and the error
codes.

Unlike IdlCheck.lean, nothing here is a hand-written copy: a meta-program reads
the model's own definitions (the `Instruction` constructors, the extracted
`zkcash_core` structures, the constructors of the extracted `ErrorCode`) and
compares their field names, field types and order with Idl.lean, which is
generated from the IDL. Any mismatch, or any Lean type it does not know how to
translate, is an error, so `lake build` fails.

How the model's types are read in IDL terms:
  * `U8`, `U16`, `U64`, `I64`, `Option T`, `Array T n` are themselves;
  * `Slice U8` (an instruction argument) is Borsh `bytes` (`Vec<u8>`);
  * the IDL's `pubkey` is `[u8; 32]`: the extracted code keeps keys as 32 bytes
    (same Borsh encoding);
  * the `defined` argument `ExtDataMinified` is passed as its two fields
    (`extAmount`, `fee`), so it is compared field by field;
  * names: the model's `camelCase` is the program's `snake_case`.
-/
import Lean
import PrivacyCash.Model.Idl
import PrivacyCash.Model.Program
open Lean Meta Elab Command

namespace PrivacyCash.Model.InterfaceCheck
open PrivacyCash.Model.Idl

/-- `camelCase` to `snake_case` (digits stay attached: `out1` stays `out1`). -/
def snake (s : String) : String :=
  String.join (s.toList.map fun c => if c.isUpper then "_" ++ (String.singleton c.toLower) else String.singleton c)

/-- The IDL's way of writing a type, with `pubkey` read as `[u8; 32]`. -/
partial def normalize : TypeSpec → TypeSpec
  | .prim "pubkey" => .array (.prim "u8") 32
  | .array t n => .array (normalize t) n
  | .vec t => .vec (normalize t)
  | .option t => .option (normalize t)
  | t => t

/-- A `Usize` length as written by Aeneas (`n#usize`, i.e. `Usize.ofNat n _`). -/
def usizeLit (e : Expr) : MetaM Nat := do
  if e.getAppFn.isConstOf ``Aeneas.Std.Usize.ofNat then
    if let some n ← evalNat e.getAppArgs[0]! then return n
  throwError "unsupported array length {e}"

/-- A model type in IDL terms; an error for anything not listed in the header. -/
partial def typeSpecOf (t : Expr) : MetaM TypeSpec := do
  let t ← instantiateMVars t
  let args := t.getAppArgs
  match t.getAppFn.constName? with
  | some ``Aeneas.Std.U8 => return .prim "u8"
  | some ``Aeneas.Std.U16 => return .prim "u16"
  | some ``Aeneas.Std.U64 => return .prim "u64"
  | some ``Aeneas.Std.I64 => return .prim "i64"
  | some ``Option => return .option (← typeSpecOf args[0]!)
  | some ``Aeneas.Std.Array => return .array (← typeSpecOf args[0]!) (← usizeLit args[1]!)
  | some ``Aeneas.Std.Slice =>
    if args[0]!.isConstOf ``Aeneas.Std.U8 then return .prim "bytes"
    throwError "unsupported slice type {t}"
  | some ``zkcash_core.transact.Proof => return .defined "Proof"
  | _ => throwError "unsupported type {t}"

/-- The arguments of constructor `ctor` after the first `skip`, as
    (snake_case name, type). -/
def ctorFields (ctor : Name) (skip : Nat) : MetaM (List (String × TypeSpec)) := do
  let info ← getConstInfo ctor
  forallTelescope info.type fun xs _ => do
    let mut out := []
    for x in xs.toList.drop skip do
      let d ← x.fvarId!.getDecl
      out := out ++ [(snake d.userName.toString, ← typeSpecOf d.type)]
    return out

/-- The IDL's fields of a type. -/
def idlType (tyName : String) : MetaM (List (String × TypeSpec)) :=
  match types.lookup tyName with
  | some fs => return fs.map fun (n, t) => (n, normalize t)
  | none => throwError "type {tyName} is not in Idl.lean"

/-- Instruction arguments in the IDL, with `ExtDataMinified` passed as its fields. -/
def idlArgs (args : List (String × TypeSpec)) : MetaM (List (String × TypeSpec)) := do
  let mut out := []
  for (n, t) in args do
    if t == .defined "ExtDataMinified" then out := out ++ (← idlType "ExtDataMinified")
    else out := out ++ [(n, normalize t)]
  return out

/-- How a type is shown in error messages. -/
def showType : TypeSpec → String
  | .prim n => n
  | .array t n => s!"[{showType t}; {n}]"
  | .vec t => s!"Vec<{showType t}>"
  | .option t => s!"Option<{showType t}>"
  | .defined n => n

/-- A field list as shown in error messages. -/
def showFields (fs : List (String × TypeSpec)) : String :=
  ", ".intercalate (fs.map fun (n, t) => s!"{n}: {showType t}")

/-- Fail unless the model's list equals the IDL's. -/
def expectEq (what : String) (model idl : List (String × TypeSpec)) : MetaM Unit := do
  unless model == idl do
    throwError "{what}: the model does not match the IDL\n  model: {showFields model}\n  IDL:   {showFields idl}"

/-! ## Instruction arguments (the `Instruction` constructors, after the accounts) -/

run_meta do
  expectEq "initialize arguments" (← ctorFields ``Instruction.initialize 1) (← idlArgs argsInitialize)
  expectEq "update_deposit_limit arguments"
    (← ctorFields ``Instruction.updateDepositLimit 1) (← idlArgs argsUpdateDepositLimit)
  expectEq "update_global_config arguments"
    (← ctorFields ``Instruction.updateGlobalConfig 1) (← idlArgs argsUpdateGlobalConfig)
  expectEq "transact arguments" (← ctorFields ``Instruction.transact 1) (← idlArgs argsTransact)

/-! ## Account data and argument types (the extracted structures) -/

run_meta do
  expectEq "Proof" (← ctorFields ``zkcash_core.transact.Proof.mk 0) (← idlType "Proof")
  expectEq "GlobalConfig" (← ctorFields ``zkcash_core.admin.GlobalConfig.mk 0) (← idlType "GlobalConfig")
  expectEq "TreeTokenAccount"
    (← ctorFields ``zkcash_core.admin.TreeTokenAccount.mk 0) (← idlType "TreeTokenAccount")
  expectEq "MerkleTreeAccount"
    (← ctorFields ``zkcash_core.merkle_tree.MerkleTreeAccount.mk 0) (← idlType "MerkleTreeAccount")
  expectEq "NullifierAccount" (← ctorFields ``AccountData.nullifier 0) (← idlType "NullifierAccount")

/-! ## Error codes

Anchor numbers an `#[error_code]` enum's variants from 6000 in declaration
order; the model's `anchorErrorCode` does the same with the extracted
`ErrorCode`. The check: the extracted variants, in order, are the IDL's errors,
and the IDL's codes are 6000, 6001, .... -/

run_meta do
  let some (.inductInfo i) := (← getEnv).find? ``zkcash_core.error.ErrorCode
    | throwError "zkcash_core.error.ErrorCode not found"
  let modelNames := i.ctors.map (·.getString!)
  unless modelNames == errors.map (·.2) do
    throwError "error codes: the model does not match the IDL\n  model: {modelNames}\n  IDL:   {errors.map (·.2)}"
  unless errors.map (·.1) == (List.range errors.length).map (6000 + ·) do
    throwError "error codes: the IDL's codes are not 6000, 6001, ...: {errors.map (·.1)}"

/-- `anchorErrorCode` gives each error its IDL code. -/
example : ∀ e : zkcash_core.error.ErrorCode,
    (errors.lookup (anchorErrorCode e) |>.isSome) = true := by
  intro e; cases e <;> decide

end PrivacyCash.Model.InterfaceCheck
