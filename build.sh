#!/bin/bash

rocq makefile -f _CoqProject theories/*.v -o Makefile
make clean
make
