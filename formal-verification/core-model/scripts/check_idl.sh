#!/usr/bin/env bash
# Fails unless the fork's IDL is byte-identical to upstream's.
# The IDL covers every instruction, argument, account (signer/writable flags,
# PDA seeds), account layout and error code, so equality means the refactor
# did not change the program's on-chain interface.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The Privacy Cash fork is the `privacy-cash` submodule at the repository root.
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
FORK="${FORK:-$REPO/privacy-cash}"
# The fork's `main` branch is upstream Privacy Cash, unmodified.
UPSTREAM_REF="${UPSTREAM_REF:-origin/main}"
OUT="$ROOT/target/idl-check"

rm -rf "$OUT" && mkdir -p "$OUT/upstream"

echo "==> Building IDL for upstream ($UPSTREAM_REF)"
git -C "$FORK" archive "$UPSTREAM_REF" anchor | tar -x -C "$OUT/upstream"
(cd "$OUT/upstream/anchor" && CARGO_TARGET_DIR="$FORK/anchor/target/idl-upstream" \
    anchor idl build -p zkcash -o "$OUT/upstream.json" > "$OUT/upstream.log" 2>&1)

echo "==> Building IDL for fork (working tree)"
(cd "$FORK/anchor" && anchor idl build -p zkcash -o "$OUT/fork.json" > "$OUT/fork.log" 2>&1)

if cmp -s "$OUT/upstream.json" "$OUT/fork.json"; then
    echo "OK: fork IDL is identical to $UPSTREAM_REF"
else
    echo "FAIL: IDL differs from $UPSTREAM_REF:"
    diff "$OUT/upstream.json" "$OUT/fork.json" || true
    exit 1
fi
