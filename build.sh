#!/bin/bash

rocq makefile -f _CoqProject -o Makefile
make clean
make -j
