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
  '';

  installPhase =
  ''
    INSTALLPATH=$out/lib/coq/${pkgs.coq_9_1.coq-version}/user-contrib/Cat

    mkdir -p $INSTALLPATH
    cp -r src/* $INSTALLPATH/

    # Remove .vos, .vok and .aux files.
    find $INSTALLPATH -name "*.vos" -o -name "*.vok" -o -name ".*.aux" | xargs rm -f
  '';
}
