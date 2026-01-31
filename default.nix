{ pkgs ? import <nixpkgs> {} }:

pkgs.stdenv.mkDerivation
{
  name = "Cat";

  src = pkgs.lib.cleanSource ./.;

  enableParallelBuilding = true;

  buildInputs =
  [
    pkgs.coq_8_20
  ];

  buildPhase =
  ''
    patchShebangs build.sh
    ./build.sh
    rm -f makefile makefile.conf .makefile.d
  '';

  installPhase =
  ''
    INSTALLPATH=$out/lib/coq/${pkgs.coq_8_20.coq-version}/user-contrib/Cat
    mkdir -p $INSTALLPATH
    cp -r * $INSTALLPATH
  '';
}
