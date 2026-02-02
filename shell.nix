{ pkgs ? import <nixpkgs> {} }:

let
  # Make "coqide" an alias for "rocqide".
  coqide-alias = pkgs.writeShellScriptBin "coqide" ''
    exec ${pkgs.coq_9_1.override { buildIde = true; }}/bin/rocqide "$@"
  '';
in

pkgs.mkShell
{
  buildInputs = with pkgs;
  [
    (coq_9_1.override { buildIde = true; })
    rocqPackages_9_1.stdlib
    coqide-alias
  ];

  shellHook =
  ''
    GREEN="\033[1;32m"
    RESET="\033[0m"

    export PROJECT_ROOT=$(pwd)
    export PS1="\n\[''${GREEN}\]Cat\''${PWD#\''$PROJECT_ROOT}>\[''${RESET}\] "

    echo ""
    echo -e "Category theory in Coq"
    echo ""
    echo -e "''${GREEN}nix build''${RESET}    — Build and install (requires Nix flakes)"
    echo -e "''${GREEN}nix develop''${RESET}  — Enter a Nix dev shell (requires Nix flakes)"
    echo -e "''${GREEN}nix-shell''${RESET}    — Enter a legacy Nix dev shell"
    echo -e "''${GREEN}./build.sh''${RESET}   — Regenerate the makefile, then build"
    echo -e "''${GREEN}make''${RESET}         — Build"
    echo -e "''${GREEN}make clean''${RESET}   — Clean build artifacts"
    echo -e "''${GREEN}coqide''${RESET}       — Start CoqIDE"
  '';
}