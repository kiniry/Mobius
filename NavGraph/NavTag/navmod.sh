#!/bin/bash

LIB=${HOME}/lib/navmod

ASPECTJ_HOME=/usr/local/aspectj1.6
JAVA_HOME=/usr/local/jdk1.6.0_10
WTK=/usr/local/WTK2.5.2
BCEL=/usr/local/java/bcel-5.2/bcel-5.2.jar

MIDP=${WTK}/lib
CLASSPATH=${MIDP}/midpapi20.jar:${MIDP}/wma11.jar:${MIDP}/mmapi.jar:${MIDP}/cldcapi10.jar
AJLIB=${ASPECTJ_HOME}/lib/aspectjrt.jar
NEEDED="org/aspectj/lang/NoAspectBoundException.class org/aspectj/lang/Signature.class"

AUX=${LIB}/comm.jar
INLINER=${LIB}/inliner.jar

TMP=/tmp/navmod$$
TMP1=${TMP}/aux1
TMP2=${TMP}/aux2
DEBUG=''

while test $# -ne 0; do
  case "$1" in
    -d)
        DEBUG='-d';;
    -o)
        shift; 
        DEST="$1";;
     *)
        SRC="$1";;
  esac
  shift
done

DEST=${DEST:-${SRC}-mod}

# No need to go further if we do not have the source application
if [ ! -f ${SRC}.jar ] ; then
	echo "There is no midlet suite named ${SRC}.jar."
	exit 1
fi
echo "Generating modified jar file."

# Create the temporary folders 
rm -rf ${TMP}
mkdir ${TMP}
mkdir ${TMP1}
mkdir ${TMP2}

# Modify the application with AspectJ
${ASPECTJ_HOME}/bin/ajc -classpath ${AJLIB}:${CLASSPATH}:${AUX} \
	-injars ${SRC}.jar ${LIB}/MarkGUI.aj \
	-outjar ${TMP}/modified.jar

# Expand the result in the first folder
unzip -qq -d ${TMP1} ${TMP}/modified.jar 

# Modify the classes with the inliner
find ${TMP1} -name '*.class' -exec java -classpath \
	 ${BCEL}:${INLINER} inliner.Inliner ${DEBUG} \
	 '{}' ';'

# Add the necessary classes (from navmark and from aspectJ)
unzip -qq -d ${TMP1}  ${AUX} -x 'META-INF*'
unzip -qq ${AJLIB} -d ${TMP1} ${NEEDED}

# Preverify the whole classes
${WTK}/bin/preverify -classpath ${CLASSPATH} -d ${TMP2} ${TMP1}
# Send back the result to first folder where resources are.
(cd ${TMP2}; tar -cf - .) | (cd ${TMP1} ; tar -xf -)
# Compress back
(cd ${TMP1}; zip -q -r ${TMP}/result.jar *)
# Deliver.
mv ${TMP}/result.jar ${DEST}.jar

# Compute jar size.
SIZE=$(wc -c < ${DEST}.jar)
# Create new jad with midlet URL and size modified.
if [ -f ${SRC}.jad ] ; then
	echo "Generating modified jad file."
	sed -e '/MIDlet-Jar-URL/ s/:.*$/:'${DEST}'.jar/' \
		-e '/MIDlet-Jar-Size/ s/:.*$/:'${SIZE}'/' \
		${SRC}.jad > ${DEST}.jad
else
	echo "No corresponding midlet suite descriptor ${SRC}.jad found."
fi
