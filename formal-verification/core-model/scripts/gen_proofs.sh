#!/usr/bin/env bash
# Regenerates formal-verification/conformance/proofs/proofs.json: the Groth16
# proofs the transact conformance scenarios submit, made with the fork's own
# test library and circuit artifacts (see proofs/gen_proofs.ts). Proofs are
# randomized, so only rerun this when the circuit, the verifying key or the
# scenarios change; then rerun scripts/check_conformance.sh --write.
#
# Needs the fork's node_modules (cd privacy-cash/anchor && yarn install).
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
FORK="${FORK:-$REPO/privacy-cash}"
SCRIPT="$REPO/formal-verification/conformance/proofs/gen_proofs.ts"

cd "$FORK/anchor"
FORK="$FORK" NODE_PATH="$FORK/anchor/node_modules" TS_NODE_TRANSPILE_ONLY=1 \
  TS_NODE_PROJECT="$FORK/anchor/tsconfig.json" ./node_modules/.bin/ts-node "$SCRIPT"
