#!/usr/bin/env bash
# Conformance: runs the compiled zkcash program (the mainnet build) in LiteSVM
# on fixed scenarios (formal-verification/conformance) and fails unless
# Tests/Conformance.lean holds exactly those traces. `lake build` then checks
# the model's `step` against every trace.
#
# Needs the IDL from scripts/check_idl.sh (run it first). The `transact`
# scenarios submit the proofs in formal-verification/conformance/proofs/
# (scripts/gen_proofs.sh makes them).
#
# Usage:  ./scripts/check_conformance.sh            (exit 0 = up to date)
#         ./scripts/check_conformance.sh --write    (regenerate the traces)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The Privacy Cash fork is the `privacy-cash` submodule at the repository root.
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
FORK="${FORK:-$REPO/privacy-cash}"
HARNESS="$REPO/formal-verification/conformance"
OUT="$ROOT/target/conformance"
IDL="$ROOT/target/idl-check/fork.json"
PROOFS="$HARNESS/proofs/proofs.json"
LEAN="$ROOT/Tests/Conformance.lean"
BEGIN='-- BEGIN GENERATED'
END='-- END GENERATED'

if [ ! -f "$IDL" ]; then
  echo "FAIL: $IDL is missing; run scripts/check_idl.sh first"
  exit 1
fi
mkdir -p "$OUT"

echo "==> Building zkcash.so from $FORK (mainnet build: no features)"
(cd "$FORK/anchor" && CARGO_TARGET_DIR="$OUT/sbf-target" cargo build-sbf \
    --manifest-path programs/zkcash/Cargo.toml --sbf-out-dir "$OUT/deploy" > "$OUT/build.log" 2>&1) \
  || { echo "FAIL: cargo build-sbf failed, see $OUT/build.log"; exit 1; }
echo "    SHA-256 $(shasum -a 256 "$OUT/deploy/zkcash.so" | cut -d' ' -f1)"

echo "==> Running the scenarios in LiteSVM"
NEW="$(cd "$HARNESS" && cargo run -q --release -- "$OUT/deploy/zkcash.so" "$IDL" "$PROOFS" \
  | sed -n "/^$BEGIN\$/,/^$END\$/p")"
if [ -z "$NEW" ]; then
  echo "FAIL: the harness printed no traces"
  exit 1
fi
OLD="$(sed -n "/^$BEGIN\$/,/^$END\$/p" "$LEAN")"

if [ "$NEW" = "$OLD" ]; then
  echo "OK: Tests/Conformance.lean holds the program's traces"
elif [ "${1:-}" = "--write" ]; then
  TMP="$(mktemp)"
  {
    sed "/^$BEGIN\$/,\$d" "$LEAN"
    printf '%s\n' "$NEW"
    sed "1,/^$END\$/d" "$LEAN"
  } > "$TMP"
  mv "$TMP" "$LEAN"
  echo "WROTE: Tests/Conformance.lean (now run lake build to check the model against it)"
else
  diff <(printf '%s\n' "$OLD") <(printf '%s\n' "$NEW") | head -20 || true
  echo "FAIL: Tests/Conformance.lean is out of date; rerun with --write"
  exit 1
fi
