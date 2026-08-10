{
  description = "Dev shell for privacy-cash (Anchor/Solana program + TS tests)";

  # Pinned to a revision where nixpkgs has solana-cli 2.3.13 and anchor 0.31.1,
  # matching the versions in anchor/README (Solana CLI 2.1.18+, Anchor 0.31.1).
  inputs.nixpkgs.url = "github:NixOS/nixpkgs/0b1aaeabd281751973b022dba022f492b3d620dc";

  outputs =
    { self, nixpkgs }:
    let
      systems = [
        "x86_64-linux"
        "aarch64-linux"
        "x86_64-darwin"
        "aarch64-darwin"
      ];
      forAllSystems = f: nixpkgs.lib.genAttrs systems (system: f nixpkgs.legacyPackages.${system});
    in
    {
      devShells = forAllSystems (pkgs: {
        default = pkgs.mkShell {
          packages =
            with pkgs;
            [
              solana-cli # solana, solana-test-validator, solana-keygen, cargo-build-sbf, ...
              anchor # anchor CLI (0.31.1)
              rustup # cargo-build-sbf manages its own Solana rustc through this
              nodejs_20
              yarn
              pkg-config
              git
            ]
            ++ lib.optionals stdenv.isDarwin [
              apple-sdk
            ];

          shellHook = ''
            # cargo-build-sbf wants to download platform-tools into its own
            # --sbf-sdk dir, which by default lives in the read-only nix
            # store. Give it a writable copy instead.
            export SBF_SDK_PATH="$HOME/.cache/solana-sbf-sdk/${pkgs.solana-cli.version}"
            if [ ! -d "$SBF_SDK_PATH" ]; then
              mkdir -p "$(dirname "$SBF_SDK_PATH")"
              cp -r ${pkgs.solana-cli}/bin/platform-tools-sdk/sbf "$SBF_SDK_PATH"
              chmod -R u+w "$SBF_SDK_PATH"
            fi

            # a default toolchain so plain `cargo`/`rustc` also work (e.g. `cargo test`)
            rustup default stable >/dev/null 2>&1 || true

            echo "solana:  $(solana --version)"
            echo "anchor:  $(anchor --version)"
            echo "node:    $(node --version)"
          '';
        };
      });
    };
}
