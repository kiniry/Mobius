# Copyright 2000, 2001, Compaq Computer Corporation
#
# This file must be sourced before running gnumake anywhere in this
# repository.  Moreover, it must be sourced in the top directory of this
# repository.
#

############################## roots ##############################

export JAVAFE_ROOT=`pwd`
if ! [ -a ${JAVAFE_ROOT}/setup.sh ]; then
    echo "Error: Must source setup.sh from the directory that contains it"
    exit 1
fi

unset ESCJ		# prevent confusion w/ escjava repository


######################### locations #########################

# @note kiniry 15 Jan 2003 - We must use JDK 1.2 as it (a) compiles to
# bytecodes that the decsrc package can parse, and (b) contains some
# classes (e.g., java.util.Arrays) on which ESC/Java depends.

export JAVA_HOME=/usr/java/jdk-1.2
export PATH=$JAVA_HOME/bin:$PATH

export CLASSDIRECTORY=${JAVAFE_ROOT}/classfiles
export SOURCEDIRECTORY=${JAVAFE_ROOT}/java
export TESTSOURCEDIRECTORY=${JAVAFE_ROOT}/test
export JAVADOC_GEN_DIR=${JAVAFE_ROOT}/doc/javadoc

export JDK_SOURCES=/usr/local/Java/src/jdk-1.2.2_012
export JDK_BINARIES=${JAVA_HOME}/jre/lib/rt.jar
export JDKBINARIES=${JDK_BINARIES}

export JML_HOME=/usr/local/Java/JML
export JML_SPECS=${JML_HOME}/specs
export JUNIT_HOME=/usr/local/Java/junit
export JUNIT_JAR=${JUNIT_HOME}/junit.jar

######################### classpaths #########################

#
# The classpath for compiling Javafe; no sources outside the repository
# should be on this list:
#

export CLASSES=${CLASSDIRECTORY}
export DECSRCLIBRARY=${JAVAFE_ROOT}/decsrclib
export CLASSPATH=${CLASSES}:${DECSRCLIBRARY}:.:

######################### java* cmds #########################

export JAVA=java
export JAVAC=javac
export JAVADOC=javadoc
