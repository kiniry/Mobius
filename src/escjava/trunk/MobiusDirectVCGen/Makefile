BCEL=`find ../ -name bcel-5.2.jar`
BICO=`find ../ -name bico.jar`
ESCJAVA=`find ../ -name escjava.jar`
JUNIT=`find ../../ -name junit.jar`
JAVAFE=`find ../../ -name Javafe2.0.5.jar`

jar: clean java
	@ echo Packing bico+
	cd tmp; jar cmf  ../bico+.mf ../bico+.jar mobius org escjava junitutils javafe tohtml
	@ echo Packing DirectVCGen
	cd tmp; jar cmf  ../DirectVCGen.mf ../DirectVCGen.jar mobius org escjava junitutils javafe tohtml
	rm -rf tmp
	mv bico+.jar DirectVCGen.jar ./jar




clean:
	@ echo Cleaning...
	@ rm -f ./jar/bico+.jar ./jar/DirectVCGen.jar

java:
	@ echo Compiling:
	mkdir -p tmp
	cd tmp; jar xf ${ESCJAVA}; 
	cd tmp; jar xf ${JUNIT}; 
	cd tmp; jar xf ${JAVAFE}; 
	cd tmp; jar xf ${BICO}
	cd src; javac -source 1.6 -sourcepath ../src -classpath ../tmp -d ../tmp `find ./ -name *.java`


