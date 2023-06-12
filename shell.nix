{ pkgs ? import <nixpkgs> {} }:

with pkgs;
  mkShell {
    name = "agda-tdpe";

    nativeBuildInputs = [
      git
      (agda.withPackages (p: [
        (p.standard-library.overrideAttrs (oldAttrs: {
          version = "1.7.1";
          src =  fetchFromGitHub {
            repo = "agda-stdlib";
            owner = "agda";
            rev = "v1.7.1";
            sha256 = "0khl12jvknsvjsq3l5cbp2b5qlw983qbymi1dcgfz9z0b92si3r0";
          };
        }))
        (p.agda-categories.overrideAttrs (oldAttrs: {
          version = "0.1.7.1";
          src =  fetchFromGitHub {
            repo = "agda-categories";
            owner = "agda";
            rev = "v0.1.7.1";
            sha256 = "1acb693ad2nrmnn6jxsyrlkc0di3kk2ksj2w9wnyfxrgvfsil7rn";
          };
        }))
      ]))
    ];
  }
