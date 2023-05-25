{ pkgs ? import <nixpkgs> {} }:

with pkgs;
  mkShell {
    name = "agda-catex";

    nativeBuildInputs = [
      git
      (agda.withPackages (p: [
        (p.standard-library.overrideAttrs (oldAttrs: {
          version = "1.7.2";
          src =  fetchFromGitHub {
            repo = "agda-stdlib";
            owner = "agda";
            rev = "v1.7.1";
            sha256 = "0khl12jvknsvjsq3l5cbp2b5qlw983qbymi1dcgfz9z0b92si3r0";
          };
        }))
        p.agda-categories
      ]))
    ];
  }
