{
  description = "privacy-cash formal verification: Charon/Aeneas dev shell for zkcash";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-24.11";
    # Pinned to a stable release rather than rolling nixos-unstable -- testing whether an
    # older/more-settled rustc avoids a currently-in-flux macOS dylib-linking issue
    # (isOSVersionAtLeast/isPlatformVersionAtLeast) hit with nixos-unstable's 2026-06-26 rustc.
    # See FORMAL_VERIFICATION_TOOLCHAIN_SETUP.md's progress log for the full diagnosis.
    flake-utils.url = "github:numtide/flake-utils";
    aeneas.url = "github:AeneasVerif/aeneas";
    # Not pinning a rev -- if `nix develop` fails to resolve `aeneas`, run
    # `nix flake show github:AeneasVerif/aeneas` and fix aeneasPkg/charonPkg below
    # to match the real output names, same as your x25519-verified README notes.
  };

  outputs = { self, nixpkgs, flake-utils, aeneas }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        aeneasPkg = aeneas.packages.${system}.default or aeneas.packages.${system}.aeneas;
        charonPkg = aeneas.packages.${system}.charon or aeneasPkg;
      in
      {
        devShells.default = pkgs.mkShell {
          buildInputs = [
            charonPkg
            aeneasPkg
            pkgs.elan
            pkgs.cargo
            pkgs.rustc
            pkgs.coreutils
            pkgs.git
          ];

          CHARON_HOME = "${charonPkg}";
          AENEAS_HOME = "${aeneasPkg}";

          shellHook = ''
            echo "privacy-cash formal-verification dev shell ready."
            echo "Target crate: ../anchor/programs/zkcash (crate name: zkcash)"
            charon --version || echo "WARNING: charon not on PATH -- check aeneasPkg/charonPkg above"
          '';
        };
      });
}
