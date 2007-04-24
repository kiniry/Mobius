#!/bin/bash
cd Formalisation; make; cd ..
jar cvf bicolano.jar `find ./ -name *.vo` defs_types.v
