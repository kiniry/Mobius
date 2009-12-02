#!/usr/bin/env bash

for file in *.tex
do
  base=${file%.*}
  echo "Processing $base"
  rubber -d $file &> /dev/null
  pdfcrop ${base}.pdf ${base}-cropped.pdf &> /dev/null
  gm convert -scale 15%x15% -density 1000 -transparent "#FFFFFF" ${base}-cropped.pdf ${base}.png &> /dev/null
done
echo "Cleaning up."
rm *.tex
rm *.pdf
echo "Done."

