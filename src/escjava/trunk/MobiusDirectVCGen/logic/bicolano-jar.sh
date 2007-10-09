#!/bin/bash
cd Formalisation; make; cd ..
jar cvf bicolano.jar `find ./Formalisation/Bicolano -name "*.v"` \
                     `find ./Formalisation/Bicolano -name "*.vo"` \
                     `find ./Formalisation/Logic -name "*.v"` \
                     `find ./Formalisation/Logic -name "*.vo"` \
                     `find ./Formalisation/Library -name "*.v"` \
                     `find ./Formalisation/Library -name "*.vo"` \
                     defs_types.v defs_tac.v
