{
  description = "CoqCat";

  inputs.nixpkgs.url = "github:NixOS/nixpkgs/nixos-25.11";

  outputs = { self, nixpkgs }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
    in
    {
      packages.${system}.default = pkgs.stdenv.mkDerivation
      {
        name = "CoqCat";
        src = ./.;

        enableParallelBuilding = true;

        buildInputs = [ pkgs.coq_8_20 ];

        buildPhase =
        ''
          patchShebangs build.sh
          ./build.sh
        '';

        installPhase =
        ''
          mkdir -p $out/lib/coq/${pkgs.coq_8_20.coq-version}/user-contrib/CoqCat
          find . -name "*.vo" -exec cp {} $out/lib/coq/${pkgs.coq_8_20.coq-version}/user-contrib/CoqCat/ \;
        '';
      };

      devShells.${system}.default = pkgs.mkShell
      {
        buildInputs = with pkgs; [ coq_8_20 coqPackages_8_20.coqide ];
        shellHook =
        ''
          export PS1="\n\[\033[1;32m\][nix:\w]\$\[\033[0m\] "

          ./build.sh
        '';
      };
    };
}