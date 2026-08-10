#!/usr/bin/env bash
# Regenerates formal-verification/vendor/ from scratch. Run from formal-verification/,
# inside `nix develop path:.` (needs cargo). See SETUP.md #1 for why
# this exists: 17 of zkcash's dependencies declare an unused `cdylib` build target that
# crashes Charon on macOS; cargo itself skips building it, Charon doesn't.
set -euo pipefail
cd "$(dirname "$0")"

CDYLIB_CRATES=(
  solana-nostd-keccak
  solana-program
  solana-zk-sdk
  spl-associated-token-account
  spl-elgamal-registry
  spl-discriminator
  spl-memo
  spl-program-error
  spl-tlv-account-resolution
  spl-token-confidential-transfer-proof-generation
  spl-token-metadata-interface
  spl-token
  spl-transfer-hook-interface
  spl-pod
  spl-token-2022
  spl-token-group-interface
  spl-type-length-value
)

CONFIG=../anchor/.cargo/config.toml
# If anchor/.cargo/config.toml already exists (e.g. re-running this script), it points
# [patch.crates-io] at this very vendor/ directory -- cargo vendor would then try to
# resolve dependencies through paths that don't exist yet. Move it aside first.
if [ -f "$CONFIG" ]; then
  mv "$CONFIG" "${CONFIG}.bak"
fi
( cd ../anchor && cargo vendor ../formal-verification/vendor )
if [ -f "${CONFIG}.bak" ]; then
  mv "${CONFIG}.bak" "$CONFIG"
fi

for crate in "${CDYLIB_CRATES[@]}"; do
  grep -v '"cdylib",' "vendor/${crate}/Cargo.toml" > "vendor/${crate}/Cargo.toml.tmp"
  mv "vendor/${crate}/Cargo.toml.tmp" "vendor/${crate}/Cargo.toml"
done

echo "Done. Now copy cargo-config.toml.template to ../anchor/.cargo/config.toml"
echo "(that file is gitignored -- it's project-specific patch config, not vendored source)."
