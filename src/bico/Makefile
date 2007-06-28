BCEL=`find ../../ -name bcel-5.2.jar`

jar: clean java
	@ echo Packing:
	cd tmp; jar xf ${BCEL}; jar cmf  ../manifest.mf ../bico.jar mobius org
	rm -rf tmp
	cp bico.jar ../implem/

jar-without-bcel: clean java
	@ echo Packing:
	cd tmp; jar cmf  ../manifest.mf ../bico.jar mobius
	rm -rf tmp


clean:
	@ echo Cleaning...
	@ rm -f bico.jar

java:
	@ echo Compiling:
	mkdir -p tmp
	cd src; javac -source 1.5 -sourcepath ../src -classpath  ${BCEL} -d ../tmp `find ./ -name *.java`
