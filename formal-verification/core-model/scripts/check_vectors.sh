#!/usr/bin/env bash
# Fails unless the test vectors in Tests/*.lean are exactly what the program's
# Rust code produces now. The vectors are printed by the generators in the
# fork's `programs/zkcash/tests/model_vectors/mod.rs`; each Lean file's `#guard`s
# then check the Lean model against them (at `lake build`).
#
# Usage:  ./scripts/check_vectors.sh            (exit 0 = up to date)
#         ./scripts/check_vectors.sh --write    (regenerate the Lean files)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The Privacy Cash fork is the `privacy-cash` submodule at the repository root.
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
FORK="${FORK:-$REPO/privacy-cash}"
BEGIN='-- BEGIN GENERATED'
END='-- END GENERATED'

# generator test  ->  Lean file it fills
PAIRS=(
  "print_negate_g1_vectors Tests/Bn254Vectors.lean"
  "print_field_vectors Tests/FieldVectors.lean"
  "print_account_spaces Tests/AccountSpaces.lean"
)

status=0
for pair in "${PAIRS[@]}"; do
  read -r gen file <<< "$pair"
  LEAN="$ROOT/$file"
  echo "==> $gen -> $file"
  NEW="$(cd "$FORK/anchor" && cargo test -q -p zkcash --test mod "$gen" \
    -- --ignored --nocapture 2>/dev/null | sed -n "/^$BEGIN\$/,/^$END\$/p")"
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
