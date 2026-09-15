#!/usr/bin/env bash
# Checks that the verifying key transcribed into the Lean model is byte for byte the
# VERIFYING_KEY the program is compiled with.
#
# Why this exists. The five FV_VK_* constants in curve_shim.rs are derived from
# `utils::VERIFYING_KEY` by const-eval, so on the Rust side they cannot drift. But
# `curve_shim` is --opaque, so Aeneas never sees their bytes, and the Lean model gets them
# from a HAND COPY in lean/code_model/hand_written/TrustedFuns.lean (between the
# "BEGIN VERIFYING KEY" and "END VERIFYING KEY" markers). A hand copy can drift -- a key
# rotation in utils.rs would leave the model silently proving things about the old key.
# This script is the link: it reads both files and fails unless every field matches.
#
# It parses the Rust independently of however the Lean was produced, and compares field by
# field (alpha, beta, gamme, delta, ic, in that order), so a byte moved between fields fails
# too, not just a changed byte.
#
# Usage:  ./check_vk_transcription.sh          (exit 0 = identical)
#         RUST=... LEAN=... ./check_vk_transcription.sh   (check other copies)
set -euo pipefail
cd "$(dirname "$0")"

RUST="${RUST:-../anchor/programs/zkcash/src/utils.rs}"
LEAN="${LEAN:-lean/code_model/hand_written/TrustedFuns.lean}"

# One token per line: a field name when a field starts, then that field's bytes.
rust_tokens() {
  awk '/^pub const VERIFYING_KEY/,/^};/' "$RUST" | awk '
    /Groth16Verifyingkey/ { next }   # the header line; its "16"s are not key bytes
    /nr_pubinputs:/       { next }
    /vk_alpha_g1:/        { print "alpha"; next }
    /vk_beta_g2:/         { print "beta";  next }
    /vk_gamme_g2:/        { print "gamme"; next }
    /vk_delta_g2:/        { print "delta"; next }
    /vk_ic:/              { print "ic";    next }
    { n = split($0, parts, /[^0-9]+/); for (i = 1; i <= n; i++) if (parts[i] != "") print parts[i] }'
}

lean_tokens() {
  awk '
    /BEGIN VERIFYING KEY/ { on = 1; next }
    /END VERIFYING KEY/   { on = 0; next }
    !on                   { next }
    /^def curve_shim\.FV_VK_ALPHA_G1 / { print "alpha"; next }
    /^def curve_shim\.FV_VK_BETA_G2 /  { print "beta";  next }
    /^def curve_shim\.FV_VK_GAMME_G2 / { print "gamme"; next }
    /^def curve_shim\.FV_VK_DELTA_G2 / { print "delta"; next }
    /^def curve_shim\.FV_VK_IC /       { print "ic";    next }
    /^def /                            { print "UNEXPECTED-DEF"; next }
    /^ *[0-9]/ || /\[ *[0-9]/ {
      line = $0
      while (match(line, /[0-9]+#u8/)) { print substr(line, RSTART, RLENGTH - 3); line = substr(line, RSTART + RLENGTH) }
    }' "$LEAN"
}

R=$(rust_tokens)
L=$(lean_tokens)

# Sanity: both parses found the whole key -- 5 fields, 64 + 3*128 + 8*64 = 960 bytes.
for side in R L; do
  toks="${!side}"
  fields=$(printf '%s\n' "$toks" | grep -c '^[a-z]' || true)
  bytes=$(printf '%s\n' "$toks" | grep -c '^[0-9]' || true)
  if [ "$fields" != 5 ] || [ "$bytes" != 960 ]; then
    name=$([ "$side" = R ] && echo "$RUST" || echo "$LEAN")
    echo "FAIL: parsed $fields fields / $bytes bytes from $name (expected 5 / 960)." >&2
    echo "      The file's layout changed, or the markers are missing; fix the parser or the file." >&2
    exit 1
  fi
done

if [ "$R" = "$L" ]; then
  echo "OK: verifying key in $LEAN matches $RUST (5 fields, 960 bytes)."
else
  echo "FAIL: verifying key in $LEAN differs from $RUST. First differences (field markers included):" >&2
  diff <(printf '%s\n' "$R" | nl -ba) <(printf '%s\n' "$L" | nl -ba) | head -20 >&2
  exit 1
fi
