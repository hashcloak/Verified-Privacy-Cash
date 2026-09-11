#!/usr/bin/env bash
# Reproduces the Lean model from the zkcash source and builds it.
# ONE charon run, ONE aeneas run, ONE Lean library (lean/code_model/generated).
#
# Modes:
#   ./extract.sh                regenerate the model and lake build it
#   ./extract.sh --diagnose-fr  diagnostic only: does --monomorphize let Charon translate
#                               the REAL ark-bn254 Fr (no FrShim)? Does NOT touch the model.
#
# Why this exists. extract.sh makes three charon runs and produces three libraries. But
# fv_transact_entry CALLS fv_verify_proof_full_entry and fv_check_public_amount_entry, so
# transact's closure already contains the two smaller models, and aeneas emits those
# functions again into each library. Importing two of them therefore fails:
#
#     environment already contains
#     'zkcash.utils.fv_verify_proof_full_entry_loop0_loop3.body.eq_1' from TransactShim.Funs
#
# Whole-contract theorems have to span instructions, so the union has to be one library.
# Naming every entry point as a root of a single run emits each function exactly once.
#
# SAFETY. This script writes only zkcash_model.llbc and lean/code_model/generated/. It never touches
# lean/code_model/hand_written or lean/Spec. A failed run therefore cannot damage the
# hand-written trusted base, and the *External.lean files are stashed and restored
# even if aeneas dies part-way (see the trap below).
#
# NOT YET RUN -- it needs `nix develop path:.` for charon and aeneas. Two things to watch
# on the first run are marked FIRST RUN below.
#
# Usage:
#   nix develop path:.            # then
#   ./extract.sh
#   AENEAS_STRICT=0 ./extract.sh   # tolerate aeneas errors (see below)
set -euo pipefail
cd "$(dirname "$0")"

SUBDIR=code_model/generated
LIB=code_model   # the lean_lib name in lean/lakefile.toml
LLBC=zkcash_model.llbc

# AENEAS_STRICT=1 passes -abort-on-error to aeneas. Without it aeneas reports an error on a
# function it cannot translate and CARRIES ON, dropping that function's body -- the run then
# "succeeds" with a hole in the model. curve_shim.rs records this happening already ("Aeneas
# drops the bodies of verify_proof/prepare_inputs"). With one big run a silent hole is worse,
# because everything is in the same library. Set AENEAS_STRICT=0 to see all errors at once
# instead of stopping at the first, which is what you want when diagnosing.
AENEAS_STRICT="${AENEAS_STRICT:-1}"

# Guard: never let SUBDIR name a directory that holds existing work.
case "$SUBDIR" in
  ""|Spec|code_model|code_model/hand_written)
    echo "ERROR: SUBDIR='$SUBDIR' would overwrite hand-written work. Refusing." >&2; exit 2;;
esac

MODE="regen"
if [ "${1:-}" = "--diagnose-fr" ]; then
  MODE="diagnose-fr"
elif [ -n "${1:-}" ]; then
  echo "Unknown argument: $1 (use no args, or --diagnose-fr)" >&2
  exit 2
fi

for tool in charon aeneas lake lean; do
  if ! command -v "$tool" >/dev/null 2>&1; then
    echo "ERROR: '$tool' not on PATH. Run this inside: nix develop path:." >&2
    exit 2
  fi
done

echo "Capturing a real rustc invocation for zkcash from charon's own compiler..."
CAPTURE=$(mktemp)
( cd ../anchor && RUSTFLAGS="--cap-lints=allow" charon cargo -- -v ) > "$CAPTURE" 2>&1 || true

ZKCASH_LINE=$(grep -m1 "crate-name zkcash" "$CAPTURE" || true)
if [ -z "$ZKCASH_LINE" ]; then
  echo "ERROR: didn't find a zkcash rustc invocation in charon cargo's output." >&2
  echo "See $CAPTURE for the full log." >&2
  exit 1
fi

# Strip everything up to and including "rustc ", the trailing backtick cargo's verbose
# log wraps the command in, the cdylib crate-type (we only want lib), and the
# incremental-compilation flag (not needed, can cause stale-cache confusion between runs).
ARGS=$(echo "$ZKCASH_LINE" | sed -E "s/^.*rustc //; s/\`\$//; s/--crate-type cdylib //; s/-C incremental=[^ ]+ //")
rm -f "$CAPTURE"

cd ../anchor

# ---------------------------------------------------------------------------
# Fr diagnostic (opt-in): can Charon translate the REAL Fr via monomorphization,
# instead of needing the FrShim? Targets the real zkcash::utils::check_public_amount
# (the minimal real user of ark_bn254::Fr) WITHOUT --opaque. Each variant may crash --
# that IS the experiment -- so failures are captured and reported, not fatal.
#
# NB: even a SUCCESS yields Montgomery limb arithmetic (not an abstract field), which is
# useful as a DIAGNOSIS of *why* Fr crashes, not as the production model -- see
# MODEL_REPORT.md.
# ---------------------------------------------------------------------------
if [ "$MODE" = "diagnose-fr" ]; then
  echo "=== Fr diagnostic: does --monomorphize let Charon translate the real Fr? ==="
  DIAG=../formal-verification/diagnostics
  mkdir -p "$DIAG"

  run_variant () {   # $1 = label, $2 = extra charon flags
    local label="$1" flags="$2" rc=0
    echo; echo "--- [$label] charon rustc $flags ---"
    eval "charon rustc $flags \
      --dest-file $DIAG/fr_$label.llbc \
      --start-from zkcash::utils::check_public_amount \
      --preset=aeneas -- $ARGS" > "$DIAG/fr_$label.log" 2>&1 || rc=$?
    if [ "$rc" -eq 0 ]; then
      echo "  SUCCESS -> $DIAG/fr_$label.llbc  (Fr extracted without the shim)"
    else
      echo "  FAILED (exit $rc) -- crash captured in $DIAG/fr_$label.log:"
      tail -n 8 "$DIAG/fr_$label.log" | sed 's/^/    /'
    fi
  }

  run_variant control     ""                                                     # reproduce today's crash (reference)
  run_variant mono         "--monomorphize"                                       # the main experiment
  # Also attack the trait-hierarchy suspicion. The pattern may need tuning, and may be
  # redundant with --preset=aeneas; kept because a bad flag just fails non-fatally here.
  run_variant mono_liftat  "--monomorphize --lift-associated-types 'ark_ff::*'"

  echo
  echo "=== interpretation ==="
  echo "  any variant SUCCEEDS -> Fr crash was polymorphic/const-generic handling (fixable in Charon)."
  echo "  ALL FAIL             -> crash is deeper (unsafe/intrinsics); monomorphization won't help."
  echo "  Logs + any .llbc in: formal-verification/diagnostics/"
  exit 0
fi

# --- ONE charon run, every entry point as a root -----------------------------------
# Flags are the union of what extract.sh passes to its three runs: both --opaque shims,
# plus the --exclude that works around the ErrorCode naming collision.
#
# FIRST RUN: charon 0.1.223 documents --start-from as "a list of item paths", but the
# exact CLI form (repeating the flag, as below, versus one comma-separated value) is
# untested here. If charon rejects the repetition, see the hint printed on failure.
echo "Extracting ALL entry points in ONE run..."
if ! eval "charon rustc \
  --exclude \"anchor_lang::error::{impl core::convert::From<anchor_lang::error::ErrorCode> for _}\" \
  --opaque \"zkcash::fr_shim\" \
  --opaque \"zkcash::curve_shim\" \
  --start-from zkcash::fv_transact_entry \
  --start-from zkcash::utils::fv_verify_proof_full_entry \
  --start-from zkcash::utils::fv_check_public_amount_entry \
  --dest-file ../formal-verification/$LLBC \
  --preset=aeneas -- $ARGS"; then
  cat >&2 <<'HINT'

charon failed. If the error is about --start-from being given more than once, try either
of these in the command above:

  1. one flag, comma-separated:
       --start-from 'zkcash::fv_transact_entry,zkcash::utils::fv_verify_proof_full_entry,...'

  2. a single dummy root in Rust that calls every entry point, then:
       --start-from zkcash::fv_all_entries

Note that fv_transact_entry already calls the other two, so
  --start-from zkcash::fv_transact_entry
alone produces the same closure today. The list only starts to matter when instructions
that nothing calls (initialize, update_global_config, transact_spl, ...) are added.
HINT
  exit 1
fi

cd ../formal-verification

# --- aeneas, into lean/$SUBDIR only -------------------------------------------------
# Same stash/restore discipline as extract.sh: the *External.lean files are HUMAN-OWNED
# and aeneas must never clobber them. The restore runs from a trap on EXIT, NOT inline,
# and THAT TRAP MUST NOT BE REMOVED: between the rm -rf below and the restore, a
# hand-written trusted base exists only in $BAK, so any failure in between (an aeneas
# error, a Ctrl-C) would otherwise delete it and leave the stash orphaned in /tmp.
BAK=$(mktemp -d)
for f in TypesExternal FunsExternal; do
  if [ -f "lean/$SUBDIR/$f.lean" ]; then cp "lean/$SUBDIR/$f.lean" "$BAK/$f.lean"; fi
  if [ -f "lean/$SUBDIR/${f}_Template.lean" ]; then cp "lean/$SUBDIR/${f}_Template.lean" "$BAK/${f}_Template.lean"; fi
done

restore_externals () {
  local f
  for f in TypesExternal FunsExternal; do
    if [ -f "$BAK/$f.lean" ]; then
      mkdir -p "lean/$SUBDIR"
      cp "$BAK/$f.lean" "lean/$SUBDIR/$f.lean"
      if [ -f "$BAK/${f}_Template.lean" ] && [ -f "lean/$SUBDIR/${f}_Template.lean" ] && \
         ! diff -q "$BAK/${f}_Template.lean" "lean/$SUBDIR/${f}_Template.lean" >/dev/null 2>&1; then
        echo "WARNING: lean/$SUBDIR/${f}_Template.lean changed since lean/$SUBDIR/$f.lean was" >&2
        echo "         written -- the trusted-base surface may have shifted; reconcile by hand." >&2
      fi
    elif [ -f "lean/$SUBDIR/${f}_Template.lean" ]; then
      cp "lean/$SUBDIR/${f}_Template.lean" "lean/$SUBDIR/$f.lean"
      echo "NOTE: bootstrapped lean/$SUBDIR/$f.lean from the generated template. It re-declares" >&2
      echo "      the hand-written trusted base. lean/code_model/generated/*External.lean are" >&2
      echo "      meant to be two-line forwarders into lean/code_model/hand_written/ -- if you" >&2
      echo "      are seeing this, one was lost and needs restoring, not filling in." >&2
    fi
  done
  rm -rf "$BAK"
}
trap restore_externals EXIT

rm -rf "lean/$SUBDIR"

AENEAS_FLAGS=""
if [ "$AENEAS_STRICT" = "1" ]; then AENEAS_FLAGS="-abort-on-error"; fi
aeneas "$LLBC" -backend lean -split-files -dest lean -subdir "$SUBDIR" $AENEAS_FLAGS

restore_externals
trap - EXIT

# Same aeneas a827e6f codegen workaround extract.sh applies: the derived PartialOrd `le`
# default method is emitted as `le.default <instance>`, but the pinned Aeneas Lean lib's
# le.default takes the partial_cmp FUNCTION. Binary and lib are the same revision, so
# regenerating does not fix it. Idempotent: the [^.] guard skips already-patched sites.
sed -zi -E 's/(core\.cmp\.PartialOrd\.le\.default[[:space:]]+fr_shim\.FrShim\.Insts\.CoreCmpPartialOrdFrShim)([^.])/\1.partial_cmp\2/g' "lean/$SUBDIR/Funs.lean"

# --- lakefile ----------------------------------------------------------------------
# Deliberately NOT edited here. A generation script that rewrites your build config is
# exactly what makes a broken run hard to diagnose, so this only tells you what to add.
if ! grep -q "name = \"$LIB\"" lean/lakefile.toml; then
  cat <<EOF

NEXT STEP: lean/$SUBDIR is generated but there is no lean_lib named "$LIB" in
lean/lakefile.toml, so nothing builds it. Add one whose globs cover
code_model.generated.* and code_model.hand_written.*, and add "$LIB" to defaultTargets.

EOF
fi

cd lean
export LD_LIBRARY_PATH="$(lean --print-prefix)/lib:${LD_LIBRARY_PATH:-}"
lake exe cache get
lake build

echo "Done. $LLBC and lean/$SUBDIR/ generated; nothing else was modified."
