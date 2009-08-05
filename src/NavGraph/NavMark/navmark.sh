#!/bin/bash

if [ ! -f ${JAVA_HOME}/bin/java -o ! -f ${JAVA_HOME}/bin/javac ] ; then
	echo "Are you sure JAVA_HOME points to a correctly installed SDK ? (${JAVA_HOME})"
	exit 1
fi

if [ ! -f $1.xml ]; then
	echo "Cannot find the result of the analysis for $1."
fi

JAVA=${JAVA_HOME}/bin/java 
JAVAC=${JAVA_HOME}/bin/javac
ROOT=${HOME}/lib/navmark

COMMAPI="/usr/local/java/commpai/jar/comm.jar"
JGRAPHAPI="/usr/local/java/graph-5.12/lib/jgraph.jar"

SERIAL=/tmp/serial

${JAVA} -classpath ${COMMAPI}:${JGRAPHAPI}:${LIB}/navmark.jar -DSERIAL=${SERIAL} navmid.ui.Main $1.xml