{
  description = "A basic flake with a shell";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    { nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = import nixpkgs {
          inherit system;
        };

        sources = pkgs.callPackage ./_sources/generated.nix { };

        # 一応動く
        oj-verify = with pkgs.python3Packages; pkgs.python3Packages.buildPythonApplication {
          name = "verification-helper";
          version = "5.6.0";
          pyproject = true;
          src = sources.oj-verify.src;
          build-system = [ setuptools ];
          dependencies = [
            colorlog
            importlab
            online-judge-tools
            pyyaml
            setuptools
            toml
          ];
          propagatedBuildInputs = [ setuptools ];
        };
      in
      {
        devShells.default =
          with pkgs;
          mkShell {
            # TODO: `buildInputs`, `packages` の使い分け？
            buildInputs = [
              pkg-config
              cabal-install
              llvmPackages.bintools
            ];

            packages = [
              just
              nvfetcher
              oj-verify
              (haskell.compiler.ghc984.override { useLLVM = true; })
            ];
          };

        # TODO: `nix run` からビルド・実行できるようにする？
      }
    );
}
