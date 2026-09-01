#!/usr/bin/env bash
# Reproduces the Lean model (TransactShim + CheckPublicAmountShim + VerifyProofShim)
# from the zkcash source and builds it. Run from formal-verification/, inside
# `nix develop path:.`.
# Requires setup-vendor.sh + cargo-config.toml.template only if charon hits the cdylib
# link error (reproduced on macOS AND on Linux/Manjaro; see SETUP.md Part 2).
#
# Modes:
#   ./extract.sh                regenerate the model (charon -> .llbc -> aeneas -> lean),
#                               materialize the *External imports, then `lake build` it.
#   ./extract.sh --diagnose-fr  diagnostic: does --monomorphize let Charon
#                               translate the REAL ark-bn254 Fr (no FrShim)? Reports
#                               success/failure per variant; does NOT touch the model.
#
# The tricky part this script exists to avoid redoing by hand: charon rustc needs .rlib
# files built by charon's *own* bundled compiler (a plain `cargo build` produces
# incompatible metadata -- see SETUP.md). The only reliable source for matching .rlib
# paths is charon's own build attempt, captured via -v. That attempt necessarily fails
# (charon cargo hits the cdylib linker issue on zkcash itself, see SETUP.md #2) --
# what we need is the verbose command line it prints just before failing, not a
# successful run.
set -euo pipefail
cd "$(dirname "$0")"

MODE="regen"
if [ "${1:-}" = "--diagnose-fr" ]; then
  MODE="diagnose-fr"
elif [ -n "${1:-}" ]; then
  echo "Unknown argument: $1 (use no args, or --diagnose-fr)" >&2
  exit 2
fi

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

# ---------------------------------------------------------------------------
# Normal path: regenerate the model.
# ---------------------------------------------------------------------------
echo "Extracting check_public_amount..."
eval "charon rustc --opaque \"zkcash::fr_shim\" \
  --dest-file ../formal-verification/check_public_amount_shim.llbc \
  --start-from zkcash::utils::fv_check_public_amount_entry \
  --preset=aeneas -- $ARGS"

echo "Extracting transact..."
eval "charon rustc \
  --exclude \"anchor_lang::error::{impl core::convert::From<anchor_lang::error::ErrorCode> for _}\" \
  --opaque \"zkcash::fr_shim\" \
  --opaque \"zkcash::curve_shim\" \
  --dest-file ../formal-verification/transact_shim.llbc \
  --start-from zkcash::fv_transact_entry \
  --preset=aeneas -- $ARGS"

# verify_proof, via curve_shim (see curve_shim.rs for why the shim is required:
# --opaque/--exclude on ark_ff/ark_ec/num_bigint does NOT work, because those types
# stay in the signatures of the code we want and Aeneas then drops its bodies).
# fv_transact_entry now CALLS fv_verify_proof_full_entry, so the transact model above
# already contains all of this. This separate, much smaller target is kept because it is
# far easier to develop the curve_shim assumptions against than the full transact model.
echo "Extracting verify_proof..."
eval "charon rustc \
  --opaque \"zkcash::curve_shim\" \
  --dest-file ../formal-verification/verify_proof_shim.llbc \
  --start-from zkcash::utils::fv_verify_proof_full_entry \
  --preset=aeneas -- $ARGS"

cd ../formal-verification

# The *External.lean files are HUMAN-OWNED (this is where FrShim etc. get their real
# ZMod definitions -- the trusted base). aeneas only ever regenerates Types.lean,
# Funs.lean, and the *External_Template.lean scaffolding; it must NOT clobber hand-filled
# *External.lean. So stash any existing *External.lean (and the current templates, to
# detect drift) before the rm, then restore them afterwards.
FV_MODULES="TransactShim CheckPublicAmountShim VerifyProofShim"
BAK=$(mktemp -d)
for m in $FV_MODULES; do
  for f in TypesExternal FunsExternal; do
    if [ -f "lean/$m/$f.lean" ]; then cp "lean/$m/$f.lean" "$BAK/${m}__$f.lean"; fi
    if [ -f "lean/$m/${f}_Template.lean" ]; then cp "lean/$m/${f}_Template.lean" "$BAK/${m}__${f}_Template.lean"; fi
  done
done

# Restore/bootstrap the *External.lean files the lakefile imports:
#   - if a hand-filled copy was stashed, RESTORE it (never clobber human work), and warn
#     if the freshly-generated template's trusted-base surface changed vs the stashed one
#     (a signal the restored file may need manual reconciliation);
#   - otherwise bootstrap it from the freshly-generated template.
#
# Run from a trap on EXIT, not inline, and DO NOT REMOVE THAT TRAP. Between the `rm -rf`
# below and this restore, the hand-written trusted base exists ONLY in $BAK. This script
# runs under `set -e`, so any failure in between (an aeneas error, a Ctrl-C) used to abort
# with the files deleted and the stash orphaned in /tmp -- and because the NEXT run then
# found nothing to stash, it silently "bootstrapped" the trusted base from the empty
# templates, replacing real definitions with bare axioms. That destroys the least
# reproducible work in the repo and only shows up later as a broken proof in Spec/.
restore_externals () {
  local m f
  for m in $FV_MODULES; do
    for f in TypesExternal FunsExternal; do
      if [ -f "$BAK/${m}__$f.lean" ]; then
        mkdir -p "lean/$m"
        cp "$BAK/${m}__$f.lean" "lean/$m/$f.lean"
        if [ -f "$BAK/${m}__${f}_Template.lean" ] && [ -f "lean/$m/${f}_Template.lean" ] && \
           ! diff -q "$BAK/${m}__${f}_Template.lean" "lean/$m/${f}_Template.lean" >/dev/null 2>&1; then
          echo "WARNING: lean/$m/${f}_Template.lean changed since lean/$m/$f.lean was written --" >&2
          echo "         the trusted-base surface may have shifted; reconcile lean/$m/$f.lean by hand." >&2
        fi
      elif [ -f "lean/$m/${f}_Template.lean" ]; then
        cp "lean/$m/${f}_Template.lean" "lean/$m/$f.lean"
      fi
    done
  done
  rm -rf "$BAK"
}
trap restore_externals EXIT

rm -rf lean/CheckPublicAmountShim lean/TransactShim lean/VerifyProofShim
aeneas check_public_amount_shim.llbc -backend lean -split-files -dest lean -subdir CheckPublicAmountShim
aeneas transact_shim.llbc -backend lean -split-files -dest lean -subdir TransactShim
aeneas verify_proof_shim.llbc -backend lean -split-files -dest lean -subdir VerifyProofShim

restore_externals
trap - EXIT

# Work around an aeneas a827e6f codegen bug: the derived PartialOrd `le` default method
# is emitted as `le.default <instance>`, but the pinned Aeneas Lean lib's le.default takes
# the `partial_cmp` FUNCTION, not the instance. Binary and lib are the SAME rev (a827e6f),
# so this is an internal inconsistency -- REGENERATING DOES NOT FIX IT. Append `.partial_cmp`
# at each le.default site so the model typechecks. (Idempotent: the `[^.]` guard skips
# already-patched sites.) See MODEL_REPORT.md's "What is open".
for m in $FV_MODULES; do
  sed -zi -E 's/(core\.cmp\.PartialOrd\.le\.default[[:space:]]+fr_shim\.FrShim\.Insts\.CoreCmpPartialOrdFrShim)([^.])/\1.partial_cmp\2/g' "lean/$m/Funs.lean"
done

# Build the regenerated model. LD_LIBRARY_PATH guards this box's bundled-clang crash;
# `cache get` is a no-op once Mathlib's oleans are present.
cd lean
export LD_LIBRARY_PATH="$(lean --print-prefix)/lib:${LD_LIBRARY_PATH:-}"
lake exe cache get
lake build

echo "Done. lean/{TransactShim,CheckPublicAmountShim,VerifyProofShim}/ regenerated AND built."
