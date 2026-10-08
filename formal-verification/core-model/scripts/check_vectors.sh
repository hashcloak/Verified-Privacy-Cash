#!/usr/bin/env bash
# Fails unless the test vectors in Tests/Bn254Vectors.lean are exactly what the
# program's Rust code produces now. The vectors are printed by the fork's
# `programs/zkcash/tests/model_vectors.rs`; the Lean file's `#guard`s then check
# the Lean model against them (at `lake build`).
#
# Usage:  ./scripts/check_vectors.sh            (exit 0 = up to date)
#         ./scripts/check_vectors.sh --write    (regenerate the Lean file)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The Privacy Cash fork is the `privacy-cash` submodule at the repository root.
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
FORK="${FORK:-$REPO/privacy-cash}"
LEAN="$ROOT/Tests/Bn254Vectors.lean"
BEGIN='-- BEGIN GENERATED'
END='-- END GENERATED'

echo "==> Running the generator (SolanaBn254::negate_g1)"
NEW="$(cd "$FORK/anchor" && cargo test -q -p zkcash --test mod print_negate_g1_vectors \
  -- --ignored --nocapture 2>/dev/null | sed -n "/^$BEGIN\$/,/^$END\$/p")"
if [ -z "$NEW" ]; then
  echo "FAIL: the generator printed no vectors (does it still compile?)"
  exit 1
fi
OLD="$(sed -n "/^$BEGIN\$/,/^$END\$/p" "$LEAN")"

if [ "$NEW" = "$OLD" ]; then
  echo "OK: $LEAN matches the program's negate_g1"
elif [ "${1:-}" = "--write" ]; then
  TMP="$(mktemp)"
  {
    sed "/^$BEGIN\$/,\$d" "$LEAN"
    printf '%s\n' "$NEW"
    sed "1,/^$END\$/d" "$LEAN"
  } > "$TMP"
  mv "$TMP" "$LEAN"
  echo "WROTE: $LEAN (now run lake build to check the model against it)"
else
  diff <(printf '%s\n' "$OLD") <(printf '%s\n' "$NEW") | head -20 || true
  echo "FAIL: vectors in $LEAN are out of date; rerun with --write"
  exit 1
fi
