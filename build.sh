#!/bin/bash

coq_makefile -R "." Cat -o makefile $(find . -name "*v")

make

rm makefile makefile.conf
