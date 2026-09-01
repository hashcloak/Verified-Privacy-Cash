{
  description = "privacy-cash formal verification: Charon/Aeneas dev shell for zkcash";

  inputs = {
    # Exact revisions of all three are pinned in flake.lock; `nix flake update` moves them.
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    flake-utils.url = "github:numtide/flake-utils";
    aeneas.url = "github:AeneasVerif/aeneas";
  };

  outputs = { nixpkgs, flake-utils, aeneas, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            aeneas.packages.${system}.charon   # charon: Rust -> .llbc
            aeneas.packages.${system}.default  # aeneas: .llbc -> Lean
            pkgs.elan                          # lean/lake, per lean/lean-toolchain
            pkgs.cargo                         # `charon cargo`, and setup-vendor.sh's `cargo vendor`
            pkgs.rustc                         # cargo's dependency resolution queries it
            pkgs.git                           # lake fetches the Aeneas Lean backend over git
          ];

          shellHook = ''
            echo "formal-verification dev shell. ./extract.sh regenerates the Lean model."
          '';
        };
      });
}
