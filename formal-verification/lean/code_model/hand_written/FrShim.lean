-- SHARED trusted base: FrShim operations, all DERIVED (real definitions over
-- `ZMod bn254_r`, nothing assumed).
--
-- Previously duplicated verbatim between TransactShim and CheckPublicAmountShim; the
-- bodies were byte-identical, only the docstrings differed. `from_le_bytes_mod_order`
-- existed only in TransactShim (it is the one `transact` needs and
-- `check_public_amount` does not) and is kept here for both.
import code_model.hand_written.Bn254
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false

/-- DERIVED. FrShim `==` : PartialEq via decidable equality in the field. -/
def fr_shim.FrShim.Insts.CoreCmpPartialEqFrShim.eq
  (a b : fr_shim.FrShim) : Result Bool :=
  ok (decide (a = b))

/-- DERIVED. FrShim::from_u64 : embed a `u64` into 𝔽ᵣ (values < 2⁶⁴ « r, so injective here). -/
def fr_shim.FrShim.from_u64 (x : Std.U64) : Result fr_shim.FrShim :=
  ok (x.val : ZMod bn254_r)

/-- DERIVED. FrShim::from_be_bytes_mod_order : decode the 32 bytes BIG-ENDIAN into a Nat,
    then reduce mod r. (Most-significant byte first → `acc*256 + byte`.) -/
def fr_shim.FrShim.from_be_bytes_mod_order
  (bytes : Array Std.U8 32#usize) : Result fr_shim.FrShim :=
  ok (((bytes.val.foldl (fun acc byte => acc * 256 + byte.val) 0 : ℕ)) : ZMod bn254_r)

/-- DERIVED. FrShim::from_le_bytes_mod_order : decode the 32 bytes LITTLE-ENDIAN into a Nat,
    then reduce mod r. `foldr` so the LAST byte is the most significant one, mirroring the
    big-endian version above. `transact` uses this on the locally recomputed ext-data hash
    and the big-endian one on the hash carried in the proof -- the endianness difference
    between those two call sites is real, and is exactly what this pair records. -/
def fr_shim.FrShim.from_le_bytes_mod_order
  (bytes : Array Std.U8 32#usize) : Result fr_shim.FrShim :=
  ok (((bytes.val.foldr (fun byte acc => acc * 256 + byte.val) 0 : ℕ)) : ZMod bn254_r)

/-- DERIVED. FrShim `+` : field addition. -/
def fr_shim.FrShim.Insts.CoreOpsArithAddFrShimFrShim.add
  (a b : fr_shim.FrShim) : Result fr_shim.FrShim :=
  ok (a + b)

/-- DERIVED. FrShim `-` : field subtraction. -/
def fr_shim.FrShim.Insts.CoreOpsArithSubFrShimFrShim.sub
  (a b : fr_shim.FrShim) : Result fr_shim.FrShim :=
  ok (a - b)

/-- DERIVED. FrShim unary `-` : field negation (`-a = r - a`). -/
def fr_shim.FrShim.Insts.CoreOpsArithNegFrShim.neg
  (a : fr_shim.FrShim) : Result fr_shim.FrShim :=
  ok (-a)

/-- DERIVED. FrShim partial_cmp : compare the CANONICAL representatives (0..r−1), matching
    ark-ff's ordering on `Fr`. This is what the deposit guard `amount ≤ fee` uses. -/
def fr_shim.FrShim.Insts.CoreCmpPartialOrdFrShim.partial_cmp
  (a b : fr_shim.FrShim) : Result (Option Ordering) :=
  ok (some (compare (ZMod.val a) (ZMod.val b)))
