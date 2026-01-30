#!/bin/sh

coq_makefile -f _CoqProject -o makefile $(find . -name "*v")

# Use NIX_BUILD_CORES if set (nix build), otherwise use nproc (manual)
if [ -n "$NIX_BUILD_CORES" ]; then
  JOBS=$NIX_BUILD_CORES
else
  JOBS=$(nproc)
fi

make -j $JOBS

