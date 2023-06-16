{
  description = "TDPE in Agda";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils }:
    flake-utils.lib.eachDefaultSystem (system:
      with import nixpkgs { inherit system; };
      {
        devShell = mkShell {
          packages = [
            (agda.withPackages (p: with p; [
              standard-library
              agda-categories
            ]))
          ];
        };
      }
    );
}
