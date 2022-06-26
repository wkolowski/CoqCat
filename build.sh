#!/bin/sh

coq_makefile -R "." Cat -o makefile $(find . -name "*v")

make -j `nproc`

rm makefile makefile.conf
