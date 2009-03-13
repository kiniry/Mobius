#BCEL=`find ../ -name bcel-5.2.jar`
BCEL=./lib/bcel-5.2.jar
CLOPS_RUNTIME=./lib/clops-runtime.jar
CLOPS=./lib/clops.jar
TMP=tmp
CLASSPATH=.:../${TMP}:../${BCEL}:../${CLOPS_RUNTIME}

# bico packing, needs bcel jar and the clops runtime on its path

dist/bico.jar: java
	@ echo Packing $@:
	mkdir -p dist
	cd ${TMP}; jar cmf  ../bico.mf ../$@ mobius
	rm -rf ${TMP}
	cp ${BCEL} ${CLOPS_RUNTIME} dist/

clean:
	@ echo Cleaning...
	@ rm -rf dist
	@ rm -rf ${TMP}

java: prepare
	@ echo Compiling:
	mkdir -p tmp
	cd src; javac -source 1.6 -sourcepath ../src -classpath ${CLASSPATH} -d ../${TMP} `find ./ -name *.java`
	cd clops; javac -source 1.6 -sourcepath ../clops -classpath ${CLASSPATH} -d ../${TMP} `find ./ -name *.java`
	
prepare:
	@ echo Preparing:
	java -jar lib/clops.jar bico.clops -d bico.html -c html.vm -o clops/mobius/bico/options -p mobius.bico.options 
try:
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


