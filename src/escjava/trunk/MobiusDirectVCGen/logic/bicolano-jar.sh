#!/bin/bash
cd Formalisation; make
jar cvf bicolano.jar `find ./ -name *.vo` defs_types.v
