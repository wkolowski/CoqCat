{ pkgs ? import <nixpkgs> {} }:

pkgs.mkShell
{
  buildInputs = with pkgs;
  [
    coq_8_20
    coqPackages_8_20.coqide
  ];

  shellHook =
  ''
    echo "Coq 8.20.1 development environment."
    echo "Run './build.sh' to build or 'coqide' to start the IDE."
  '';
}
