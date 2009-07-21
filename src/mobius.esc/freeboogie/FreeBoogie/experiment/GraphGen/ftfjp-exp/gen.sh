#!/bin/bash
for i in `seq 0 999`; do java -jar ../dist/lib/graphgen.jar -d 10 -do $i.bot -bo $i.bpl -s $i; done > gen.log
