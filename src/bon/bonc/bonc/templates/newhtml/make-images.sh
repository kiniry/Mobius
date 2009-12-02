#!/usr/bin/env bash

rubber -d *.tex
for file in *.tex
do
  base=${file%.*}
  echo "Resizing $base"
  pdfcrop ${base}.pdf ${base}-cropped.pdf &> /dev/null
  echo "Converting $base to .png"
  gm convert -scale 15%x15% -density 1000 -transparent "#FFFFFF" ${base}-cropped.pdf ${base}.png &> /dev/null
done
echo "Cleaning up."
rm *.tex
rm *.pdf
rm *.aux
rm *.log
echo "Done."
