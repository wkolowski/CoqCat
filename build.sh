#!/bin/sh

# If the makefile is missing or _CoqProject has changed, regenerate the makefile.
if [ ! -f makefile ] || [ _CoqProject -nt makefile ]
then
  echo "Regenerating makefile..."
  coq_makefile -f _CoqProject -o makefile $(find src -name "*.v")
fi


# Determine the numbers of CPU cores on which the build will run in parallel.
if [ -n "$NIX_BUILD_CORES" ]
then
  # If building using `nix build`, use NIX_BUILD_CORES.
  JOBS=$NIX_BUILD_CORES
else
  # If building manually (using `./build.sh` or `make`), use all available CPU cores.
  JOBS=$(nproc)
fi

make -j $JOBS
