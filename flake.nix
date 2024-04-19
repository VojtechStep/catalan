{
  description = "Catalan numbers";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs?ref=nixos-unstable";
    lean.url = "github:leanprover/lean4?ref=v4.6.0";
  };

  outputs = { self, nixpkgs, lean }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      leanPkgs = lean.packages.${system};
    in
    {
      devShells.${system}.default =
        pkgs.mkShell {
          name = "catalean";
          packages = [
            pkgs.elan
          ];

          env.LEAN_MODE = "${leanPkgs.lean4-mode}/share/emacs/site-lisp/elpa/lean4-mode-1";
        };
    };
}
