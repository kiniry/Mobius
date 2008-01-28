#!/bin/bash
echo "Generating javac.jar"
echo "Looking for langtools..."
if [ -n $LANGTOOLS_ROOT ] 
then 
	echo "LANGTOOLS_ROOT variable is not set, consider adding it"
	LANGTOOLS_ROOT="../../langtools"
fi
echo "LANGTOOLS_ROOT is set to $LANGTOOLS_ROOT"
here=`pwd`
cd $LANGTOOLS_ROOT/bin
jar cvfe ${here}/javac.jar com.sun.tools.javac.Main *
