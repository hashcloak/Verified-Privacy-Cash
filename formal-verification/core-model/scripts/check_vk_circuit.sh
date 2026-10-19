#!/usr/bin/env bash
# Fails unless the program's verifying key (zkcash_core::verifying_key, the key
# the Lean model's verifier uses) is the circuit's: the key exported with
# snarkjs from the circuit's proving key, artifacts/circuits/transaction2.zkey,
# byte for byte. Also fails if the committed verifyingkey2.json has drifted
# from that export.
#
# Points are encoded as the alt_bn128 syscalls read them: G1 as x || y, G2 as
# x.c1 || x.c0 || y.c1 || y.c0, each coordinate 32 bytes big-endian.
#
# Usage: ./scripts/check_vk_circuit.sh   (uses the fork's snarkjs, or npx snarkjs@0.7.5)
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
REPO="$(git -C "$ROOT" rev-parse --show-toplevel)"
FORK="${FORK:-$REPO/privacy-cash}"
CIRCUITS="$FORK/artifacts/circuits"
OUT="$ROOT/target/vk-circuit"
mkdir -p "$OUT"

if [ -x "$FORK/anchor/node_modules/.bin/snarkjs" ]; then
  SNARKJS=("$FORK/anchor/node_modules/.bin/snarkjs")
else
  SNARKJS=(npx --yes snarkjs@0.7.5)
fi
echo "==> Exporting the verifying key from transaction2.zkey"
"${SNARKJS[@]}" zkey export verificationkey "$CIRCUITS/transaction2.zkey" "$OUT/vk.json" > "$OUT/export.log" 2>&1 \
  || { echo "FAIL: snarkjs export failed, see $OUT/export.log"; exit 1; }

python3 - "$OUT/vk.json" "$FORK/anchor/crates/zkcash_core/src/verifying_key.rs" "$CIRCUITS/verifyingkey2.json" <<'PY'
import json, re, sys
vk = json.load(open(sys.argv[1]))
src = open(sys.argv[2]).read()
committed = json.load(open(sys.argv[3]))

def be(n): return list(int(n).to_bytes(32, "big"))
def g1(p):
    assert p[2] == "1", "G1 point not in affine form"
    return be(p[0]) + be(p[1])
def g2(p):
    assert p[2] == ["1", "0"], "G2 point not in affine form"
    (x0, x1), (y0, y1) = p[0], p[1]
    return be(x1) + be(x0) + be(y1) + be(y0)

assert vk["protocol"] == "groth16" and vk["curve"] == "bn128", "not a Groth16 BN254 key"
assert vk["nPublic"] == 7 and len(vk["IC"]) == 8, "not 7 public inputs"
expected = {
    "vk_alpha_g1": g1(vk["vk_alpha_1"]),
    "vk_beta_g2": g2(vk["vk_beta_2"]),
    "vk_gamme_g2": g2(vk["vk_gamma_2"]),
    "vk_delta_g2": g2(vk["vk_delta_2"]),
    "vk_ic": sum((g1(p) for p in vk["IC"]), []),
}
body = src[src.index("pub const VERIFYING_KEY"):]
names = list(expected)
ok = True
for i, name in enumerate(names):
    start = body.index(name + ":") + len(name) + 1
    end = body.index(names[i + 1] + ":") if i + 1 < len(names) else body.index("};")
    got = [int(x) for x in re.findall(r"\d+", body[start:end])]
    if got != expected[name]:
        ok = False
        print(f"FAIL: {name} differs from the circuit's key ({len(got)} vs {len(expected[name])} bytes)")
if committed != vk:
    ok = False
    print("FAIL: artifacts/circuits/verifyingkey2.json is not the key exported from transaction2.zkey")
if not ok:
    sys.exit(1)
print("OK: the program's verifying key is the circuit's (960 bytes); verifyingkey2.json matches")
PY
