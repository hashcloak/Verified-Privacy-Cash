#!/usr/bin/env bash
# End-to-end differential check: runs upstream's TypeScript integration suites
# (real Groth16 proofs, real transactions) against the fork's compiled program
# and against upstream's, each on a fresh local validator, and fails unless
# both pass every test.
#
# The program is loaded at its localnet address with `--bpf-program`, so the
# (private) program keypair is not needed.
#
# Usage: ./scripts/e2e.sh            (suites: sol_tests spl_tests)
#        SUITES=sol_tests ./scripts/e2e.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
# The Privacy Cash fork is the `privacy-cash` submodule at the repository root.
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
FORK="${FORK:-$REPO/privacy-cash}"
# The fork's `main` branch is upstream Privacy Cash, unmodified.
UPSTREAM_REF="${UPSTREAM_REF:-origin/main}"
SUITES="${SUITES:-sol_tests spl_tests}"
WORK="$ROOT/target/e2e"
PROGRAM_ID="ATZj4jZ4FFzkvAcvk27DW9GRkgSbFnHo49fKKPQXU7VS"
RPC="http://127.0.0.1:8899"

rm -rf "$WORK/upstream" "$WORK/ledger" && mkdir -p "$WORK/upstream" "$WORK/logs"
WALLET="$WORK/wallet.json"
[ -f "$WALLET" ] || solana-keygen new --no-bip39-passphrase --silent -o "$WALLET" > /dev/null

stop_validator() { pkill -f "solana-test-validator.*$WORK/ledger" 2> /dev/null || true; sleep 2; }
trap stop_validator EXIT

echo "==> Installing test dependencies (fork)"
(cd "$FORK/anchor" && [ -d node_modules ] || npm ci --no-audit --no-fund > "$WORK/logs/npm.log" 2>&1)

echo "==> Building fork program"
(cd "$FORK/anchor" && anchor build -- --features localnet > "$WORK/logs/build-fork.log" 2>&1)

echo "==> Building upstream program ($UPSTREAM_REF)"
git -C "$FORK" archive "$UPSTREAM_REF" | tar -x -C "$WORK/upstream"
ln -s "$FORK/anchor/node_modules" "$WORK/upstream/anchor/node_modules"
(cd "$WORK/upstream/anchor" && CARGO_TARGET_DIR="$FORK/anchor/target/e2e-upstream" \
    anchor build -- --features localnet > "$WORK/logs/build-upstream.log" 2>&1)
mkdir -p "$WORK/upstream/anchor/target"
cp -r "$FORK/anchor/target/e2e-upstream/deploy" "$WORK/upstream/anchor/target/"

# run_once <name> <anchor dir> <suite>: prints "<passing> <failing>"
run_once() {
    local name=$1 dir=$2 suite=$3 log="$WORK/logs/$1-$3.log"
    stop_validator
    solana-test-validator --reset --quiet --ledger "$WORK/ledger" \
        --bpf-program "$PROGRAM_ID" "$dir/target/deploy/zkcash.so" > "$WORK/logs/validator.log" 2>&1 &
    for _ in $(seq 1 60); do solana -u "$RPC" cluster-version > /dev/null 2>&1 && break; sleep 2; done
    sleep 5 # let the first blocks land, or early transactions fail with "Blockhash not found"
    solana -u "$RPC" airdrop 1000 "$(solana-keygen pubkey "$WALLET")" > /dev/null
    (cd "$dir" && ANCHOR_PROVIDER_URL="$RPC" ANCHOR_WALLET="$WALLET" \
        npx ts-mocha -p ./tsconfig.json -t 1000000 --exit "tests/$suite.ts" > "$log" 2>&1) || true
    local passing failing
    passing=$(grep -Eo '[0-9]+ passing' "$log" | grep -Eo '[0-9]+' || echo 0)
    failing=$(grep -Eo '[0-9]+ failing' "$log" | grep -Eo '[0-9]+' || echo 0)
    echo "$passing $failing"
}

# Upstream's suites are occasionally flaky on a local validator (tests that
# create address lookup tables can fail with "Blockhash not found"), so a
# failing suite is rerun on a fresh validator up to MAX_ATTEMPTS times in total.
# A real regression fails every attempt.
MAX_ATTEMPTS="${MAX_ATTEMPTS:-3}"

# run_suite <name> <anchor dir> <suite>: prints "<passing> <failing> <attempts>"
run_suite() {
    local attempt=1 result
    while :; do
        result=$(run_once "$@")
        if [ "${result#* }" = 0 ] || [ "$attempt" -ge "$MAX_ATTEMPTS" ]; then
            echo "$result $attempt"
            return
        fi
        cp "$WORK/logs/$1-$3.log" "$WORK/logs/$1-$3.attempt$attempt.log"
        attempt=$((attempt + 1))
    done
}

status=0
for suite in $SUITES; do
    read -r up_pass up_fail up_tries < <(run_suite upstream "$WORK/upstream/anchor" "$suite")
    read -r fork_pass fork_fail fork_tries < <(run_suite fork "$FORK/anchor" "$suite")
    echo "==> $suite: upstream $up_pass passing / $up_fail failing (attempts: $up_tries),"         "fork $fork_pass passing / $fork_fail failing (attempts: $fork_tries)"
    if [ "$fork_fail" != 0 ] || [ "$up_fail" != 0 ] || [ "$fork_pass" != "$up_pass" ] || [ "$fork_pass" = 0 ]; then
        echo "FAIL: $suite (logs in ${WORK#$ROOT/}/logs/)"
        status=1
    fi
done
[ "$status" = 0 ] && echo "OK: fork matches upstream on: $SUITES"
exit "$status"
