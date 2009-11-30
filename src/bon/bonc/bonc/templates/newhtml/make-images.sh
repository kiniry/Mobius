#!/usr/bin/env bash

for file in *.tex
do
  base=${file%.*}
  echo "Processing $base"
  rubber $file &> /dev/null
  dvips -x 250 -E ${base}.dvi -o &> /dev/null
  gm convert -density 500 -transparent "#FFFFFF" ${base}.ps ${base}.png &> /dev/null
done
echo "Cleaning up."
rm *.tex
rm *.dvi
rm *.ps
echo "Done."

