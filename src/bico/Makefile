#BCEL=`find ../ -name bcel-5.2.jar`
BCEL=./lib/bcel-5.2.jar
TMP=tmp

# bico packing, needs bcel jar on its path

bico.jar: java
	@ echo Packing $@:
	cd ${TMP}; jar cmf  ../bico.mf ../$@ mobius
	rm -rf ${TMP}

clean:
	@ echo Cleaning...
	@ rm -f bico.jar
	@ rm -rf ${TMP}

java:
	@ echo Compiling:
	mkdir -p tmp
	cd src; javac -source 1.6 -sourcepath ../src -classpath ../${BCEL} -d ../${TMP} `find ./ -name *.java`


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


