BCEL=`find ../../ -name bcel-5.2.jar`

jar: clean java
	@ echo Packing:
	cd tmp; jar xf ${BCEL}; jar cmf  ../manifest.mf ../bico.jar bico org
	rm -rf tmp

jar-without-bcel: clean java
	@ echo Packing:
	cd tmp; jar cmf  ../manifest.mf ../bico.jar bico
	rm -rf tmp


clean:
	@ echo Cleaning...
	@ rm -f bico.jar
	
java:
	@ echo Compiling:
	mkdir -p tmp
	cd src; javac -target 1.4 -source 1.4 -sourcepath ../src -classpath  ${BCEL} -d ../tmp `find ./ -name *.java`
