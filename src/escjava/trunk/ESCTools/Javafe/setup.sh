# Copyright 2000, 2001, Compaq Computer Corporation
#
# This file must be sourced before running gnumake anywhere in this
# repository.  Moreover, it must be sourced in the top directory of this
# repository.
#

############################## roots ##############################

export JAVAFE_ROOT=`pwd`
if ! [ -a ${JAVAFE_ROOT}/setup ]; then
    echo "Error: Must source setup from the directory that contains it"
    exit 1
fi

unset ESCJ		# prevent confusion w/ escjava repository


######################### locations #########################

export JAVA_HOME=/usr/java/jdk-1.1
export PATH=$JAVA_HOME/bin:$PATH

export CLASSDIRECTORY=${JAVAFE_ROOT}/classfiles
export SOURCEDIRECTORY=${JAVAFE_ROOT}/java
export JAVADOCDIRECTORY=${JAVAFE_ROOT}/doc/javadoc

export JDK_SOURCES=/usr/local/Java/src/jdk-1.18_03
export JDK_BINARIES=${JAVA_HOME}/lib/classes.zip
export JDKBINARIES=${JDK_BINARIES}

######################### classpaths #########################

#
# The classpath for compiling Javafe; no sources outside the repository
# should be on this list:
#

export CLASSES=${CLASSDIRECTORY}
export DECSRCLIBRARY=${JAVAFE_ROOT}/decsrclib

export CLASSPATH=${CLASSES}:${DECSRCLIBRARY}
# javadepend needs a classpath where all the sources are in the current dir:
export LCLASSPATH=.:${CLASSES}


######################### java* cmds #########################

#
# which version of java:
#
export JAVA=java

#
# Other java* commands:
#
export JAVAC=javac
export OLD_JAVAC=/usr/java/jdk-1.1/bin/javac
export JAVADOC=javadoc

#
# Aliases to invoke javac with proper arguments for human use:
#
alias javacd='${JAVAC} -d ${CLASSDIRECTORY}'
alias jall='javacd *.java'

#
# Fast incremental recompilation of selected classes:
#
alias jfast='(cd ${SOURCEDIRECTORY}; export CLASSPATH=${LCLASSPATH}; javadepend -d ${CLASSDIRECTORY} \!* | javamake -d ${CLASSDIRECTORY} - )'

alias sprint='swiftrun ${CLASSDIRECTORY}/compiled.zip javafe.test.Print'
