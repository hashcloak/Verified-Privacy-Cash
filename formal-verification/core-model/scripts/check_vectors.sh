#!/usr/bin/env bash
# Fails unless the test vectors in Tests/*.lean are exactly what the program's
# code produces now. Most vectors are printed by the generators in the fork's
# `programs/zkcash/tests/model_vectors/mod.rs`; the G1 decoding vectors by the
# conformance harness (`formal-verification/conformance/src/bin/g1_vectors.rs`,
# which uses the validator's solana-bn254). Each Lean file's `#guard`s then
# check the Lean model against them (at `lake build`).
#
# Usage:  ./scripts/check_vectors.sh            (exit 0 = up to date)
#         ./scripts/check_vectors.sh --write    (regenerate the Lean files)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The Privacy Cash fork is the `privacy-cash` submodule at the repository root.
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
FORK="${FORK:-$REPO/privacy-cash}"
HARNESS="$REPO/formal-verification/conformance"
BEGIN='-- BEGIN GENERATED'
END='-- END GENERATED'

# generator  ->  Lean file it fills. "fork:<test>" is a test in the fork,
# "harness:<bin>" a binary of the conformance harness.
PAIRS=(
  "fork:print_negate_g1_vectors Tests/Bn254Vectors.lean"
  "fork:print_field_vectors Tests/FieldVectors.lean"
  "fork:print_account_spaces Tests/AccountSpaces.lean"
  "harness:g1_vectors Tests/G1DecodeVectors.lean"
)

generate() {
  case "$1" in
    fork:*) (cd "$FORK/anchor" && cargo test -q -p zkcash --test mod "${1#fork:}" -- --ignored --nocapture 2>/dev/null) ;;
    harness:*) (cd "$HARNESS" && cargo run -q --release --bin "${1#harness:}" 2>/dev/null) ;;
  esac
}

status=0
for pair in "${PAIRS[@]}"; do
  read -r gen file <<< "$pair"
  LEAN="$ROOT/$file"
  echo "==> $gen -> $file"
  NEW="$(generate "$gen" | sed -n "/^$BEGIN\$/,/^$END\$/p")"
  if [ -z "$NEW" ]; then
    echo "FAIL: $gen printed no vectors (does it still compile?)"
    status=1; continue
  fi
  OLD="$(sed -n "/^$BEGIN\$/,/^$END\$/p" "$LEAN")"

  if [ "$NEW" = "$OLD" ]; then
    echo "OK: $file is up to date"
  elif [ "${1:-}" = "--write" ]; then
    TMP="$(mktemp)"
    {
      sed "/^$BEGIN\$/,\$d" "$LEAN"
      printf '%s\n' "$NEW"
      sed "1,/^$END\$/d" "$LEAN"
    } > "$TMP"
    mv "$TMP" "$LEAN"
    echo "WROTE: $file (now run lake build to check the model against it)"
  else
    diff <(printf '%s\n' "$OLD") <(printf '%s\n' "$NEW") | head -20 || true
    echo "FAIL: $file is out of date; rerun with --write"
    status=1
  fi
done
exit $status
