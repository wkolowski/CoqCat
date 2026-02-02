{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation
{
  name = "Cat";

  src = pkgs.lib.cleanSource ./.;

  enableParallelBuilding = true;

  buildInputs = with pkgs;
  [
    coq_9_1
    rocqPackages_9_1.stdlib
  ];

  buildPhase =
  ''
    patchShebangs build.sh
    ./build.sh
    rm -f makefile makefile.conf .makefile.d
  '';

  installPhase =
  ''
    INSTALLPATH=$out/lib/coq/${pkgs.coq_9_1.coq-version}/user-contrib/Cat
    mkdir -p $INSTALLPATH
    cp -r * $INSTALLPATH
  '';
}
