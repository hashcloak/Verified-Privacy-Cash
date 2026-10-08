#!/usr/bin/env bash
# Regenerates the Lean model of zkcash_core from its Rust source:
#   Rust --Charon--> LLBC --Aeneas--> PrivacyCash/Extracted/{Types,Funs}.lean
# Generated files must never be edited by hand; rerun this script instead.
# The one hand-written file there is FunsExternal.lean: Lean definitions for
# Rust library functions Aeneas does not know (listed in the regenerated
# FunsExternal_Template.lean).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The Privacy Cash fork is the `privacy-cash` submodule at the repository root.
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
CRATE="${FORK:-$REPO/privacy-cash}/anchor/crates/zkcash_core"
LLBC="$ROOT/target/llbc/zkcash_core.llbc"
DEST="$ROOT/PrivacyCash/Extracted"
CHARON="${CHARON:-$HOME/aeneas/charon/bin/charon}"
AENEAS="${AENEAS:-$HOME/aeneas/bin/aeneas}"

mkdir -p "$(dirname "$LLBC")" "$DEST"

echo "==> Charon: Rust -> LLBC"
# No --features: the optional `bytemuck` feature is for the on-chain program only.
(cd "$CRATE" && "$CHARON" cargo --preset=aeneas --dest-file "$LLBC")

echo "==> Aeneas: LLBC -> Lean"
"$AENEAS" -backend lean "$LLBC" -dest "$ROOT" -subdir PrivacyCash/Extracted -split-files

echo "==> External functions Aeneas needs (must all be defined in FunsExternal.lean):"
grep -E '^axiom ' "$DEST/FunsExternal_Template.lean" | sed 's/^/    /' || echo "    (none)"
