#BCEL=`find ../ -name bcel-5.2.jar`
BCEL=./lib/bcel-5.2.jar
CLOPS_RUNTIME=./lib/clops-runtime.jar
CLOPS=./lib/clops.jar
TMP=tmp
CLASSPATH=.:../${TMP}:../${BCEL}:../${CLOPS_RUNTIME}


	
try:
	java  -jar dist/bico.jar  test -map -list
	java  -jar dist/bico.jar  test -o tmp -cp test A

setup:
	cp -v ../CLO/dist/lib/clops* ./lib/

## old commands useless	
jar: clean java
	@ echo Packing:
	cd tmp; jar xf ${BCEL}; jar cmf  ../manifest.mf ../bico.jar mobius org
	rm -rf tmp
	cp bico.jar ../implem/

jar-without-bcel: clean java
	@ echo Packing:
	cd tmp; jar cmf  ../manifest.mf ../bico.jar mobius
	rm -rf tmp


