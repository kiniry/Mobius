BICO_WORKSPACE=../bico
ESCJ_WORKSPACE=../ESCJava2

## Bico libraries
FIND_BCEL=`find ${BICO_WORKSPACE} -name bcel-5.2.jar`
BCEL=./lib/bcel-5.2.jar
FIND_BICO=`find ${BICO_WORKSPACE} -name bico.jar`
BICO=./lib/bico.jar

## ESC/Java libs
ESCJAVA=./lib/escjava.jar
FIND_JUNIT=`find ${ESCJ_WORKSPACE} -name junit.jar`
JUNIT=./lib/junit.jar
FIND_JAVAFE=`find ${ESCJ_WORKSPACE} -name Javafe2.0.5.jar`
JAVAFE=./lib/Javafe2.0.5.jar

## Special JAVAC
MOBIUS_JAVAC=./lib/javac.jar

LIBS=${BICO}:${BCEL}:${JUNIT}:${JAVAFE}:${ESCJAVA}:${MOBIUS_JAVAC}

TMP=tmp

prepare:
	@ echo Copying Bico and its dependences:
	@ cp ${FIND_BICO} ${BICO}
	@ ls ${BICO}
	@ cp ${FIND_BCEL} ${BCEL}
	@ ls ${BCEL}
	@ echo Copying ESC/Java2 and its dependences:
	@ ls ${ESCJAVA}
	@ cp ${FIND_JUNIT} ${JUNIT}
	@ ls ${JUNIT}
	@ cp ${FIND_JAVAFE} ${JAVAFE}
	@ ls ${JAVAFE}
	@ echo Special JavaC:
	@ ls ${MOBIUS_JAVAC}
	@ echo
	@ echo "Now run 'make jar'"
	@ echo


	




clean:
	@ echo Cleaning...
	@ rm -f ./jar/bico+.jar ./jar/DirectVCGen.jar

java:
	@ echo Compiling:
	mkdir -p ${TMP}
	 javac -source 1.6 -sourcepath ./src  -classpath ${TMP}:${LIBS} -d ${TMP} `find ./src -name *.java`


