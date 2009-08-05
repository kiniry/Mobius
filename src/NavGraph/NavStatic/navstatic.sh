#!/bin/bash

if [ ! -f ${JAVA_HOME}/bin/java -o ! -f ${JAVA_HOME}/bin/javac ] ; then
	echo "Are you sure JAVA_HOME points to a correctly installed SDK ? (${JAVA_HOME})"
	exit 1
fi

JAVA=${JAVA_HOME}/bin/java 
JAVAC=${JAVA_HOME}/bin/javac
ROOT=${HOME}/lib/navstatic
LIB=${ROOT}/lib
SOOTLIB=/usr/local/java/soot
MIDP=${HOME}/lib/modsa/midp

SOOTCLASSPATH=${SOOTLIB}/jasminclasses-2.3.0.jar:${SOOTLIB}/polyglot-1.3.5.jar:${SOOTLIB}/sootclasses-2.3.0.jar:${ROOT}/navstatic.jar

TMP=/tmp/nav$$
MAIN=Launcher
WRAPPER=${TMP}/${MAIN}.java
mkdir ${TMP}

midNum=1

while test $# -ne 0; do
  case "$1" in
    -m)	shift; midNum=$1;;
     *)	JAR="$1";;
  esac
  shift
done

if [ "${JAR}" == "" ]; then
	echo "Please provide a jar file."
	exit 1
fi
if [ ! -f "${JAR}" ]; then
	echo "Cannot find Jar file ${JAR}."
	exit 1
fi

OUTPUT=${JAR%%\.jar}.xml

# The classpath used by Midlets.
MIDPCLASSPATH=${MIDP}/cldc10.jar:${MIDP}/midp20.jar:${MIDP}/wma20.jar:${MIDP}/mmapi.jar:${JAR}:

MIDLET=$(unzip -p ${JAR} META-INF/MANIFEST.MF | grep MIDlet-${midNum}: \
	| awk -F ',' '{print $3}' | tr '/' '.' | tr -d '\\f')

if [ "${MIDLET}" == "" ]; then
	echo "Cannot find a midlet in the Jar file."
	exit 1
fi

#Creates the wrappper class and compile it.
cat - > ${WRAPPER} <<EOF
class ${MAIN} {
  public static void main(String [] args) {
    try {com.francetelecom.rd.fakemidp.Runtime.run(new ${MIDLET} ());}
    catch (Exception e) {}
  }
}
EOF

${JAVAC} -classpath ${MIDPCLASSPATH} -target 1.4 -source 1.4 ${WRAPPER}

${JAVA} -classpath ${SOOTCLASSPATH} navstatic.analyze.Explorer --app -w -cp ${MIDPCLASSPATH}:${TMP} -p cg.spark 'enabled:true,string-constants:true' -keep-offset -x 'com.francetelecom.rd.fakemidp' -p wjtp.navstatic "enabled:true,output:${OUTPUT}" -f n -d ${TMP}/out -main-class ${MAIN} ${MAIN}
