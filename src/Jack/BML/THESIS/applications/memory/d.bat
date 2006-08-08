latex main.tex
bibtex main
latex main.tex

dvips main.dvi -o main.ps
gzip -f main.ps

rm -f *.dvi
rm -f *.aux
rm -f *.log
rm -f *.???~
