#!/bin/bash
# Copyright 2000, 2001, Compaq Computer Corporation
#
# This file must be sourced before running gnumake anywhere in this
# repository.  Moreover, it must be sourced in the top directory of this
# repository.
#

############################## roots ##############################

# Javafe dependencies
export JAVAFE_ROOT=`pwd`/../Javafe
export JAVAFE_CLASSFILES=${JAVAFE_ROOT}/classfiles

export ESCTOOLS_ROOT=`pwd`/..
export ESCTOOLS_JARS=${ESCTOOLS_ROOT}/jars

export ESCJAVA_ROOT=`pwd`
if ! [ -a ${ESCJAVA_ROOT}/setup ]; then
    echo "Error: Must source setup from the directory that contains it"
    exit 1
fi

if [ "$1" == "both" ]; then
    echo NOTICE: '"both"' parameter is now the default, and so is deprecated
elif [ "$1" == "javafe" ]; then
    echo Error: '"javafe"' parameter no longer supported
    exit 1
elif [ "$1" == "jdk" ]; then
    echo Error: '"jdk"' parameter no longer supported
    exit 1
fi
if [ "$1" == "houdini" ]; then
    echo -- $* --
    echo "Illegal parameter!  Usage: source setup.sh"
    exit 1
fi
    # We allow the negation of the last case as a special case, so as
    # not to generate an error when Houdini's "runesc" script is
    # invoked.

export JAVAFE_ROOT=${ESCJAVA_ROOT}/../Javafe
# If you have a more specification files (for example, if you
# downloaded more .spec files from the ESC/Java binary release), then
# change the following line to point to that spec directory.
export JDKSPEC_ROOT=${ESCJAVA_ROOT}/release/master/specs

if ! [ -d ${JAVAFE_ROOT} ]; then
    echo "Error: Javafe root not found: ${JAVAFE_ROOT}"
fi
if ! [ -d ${JDKSPEC_ROOT} ]; then
    echo "Error: JDK spec root not found: ${JDKSPEC_ROOT}"
fi

######################### locations #########################

if ! [ -d ${JAVA_HOME} ]; then
    export JAVA_HOME=/usr/java/jdk-1.2
fi
export PATH=$JAVA_HOME/bin:$PATH

export CLASSDIRECTORY=${ESCJAVA_ROOT}/classfiles
export SOURCEDIRECTORY=${ESCJAVA_ROOT}/java
export TESTSOURCEDIRECTORY=${ESCJAVA_ROOT}/test
export JAVADOCDIRECTORY=${ESCJAVA_ROOT}/doc/javadoc

export SRCDIRECTORY=${JAVAFE_ROOT}/decsrclib
export SRCCLASSDIRECTORY=${JAVAFE_ROOT}/decsrclib

#
# Where to find binaries for the JDK libraries:
#

# @note kiniry 15 Jan 2003 - We must use JDK 1.2 as it (a) compiles to
# bytecodes that the decsrc package can parse, and (b) contains some
# classes (e.g., java.util.Arrays) on which ESC/Java depends.

if [ "${JAVA_HOME}" == "/usr/java/jdk-1.2" ]; then
  export JDK_SOURCES=/usr/local/Java/src/jdk-1.2
elif [ "${JAVA_HOME}" == "/usr/java/jdk-1.3" ]; then
  export JDK_SOURCES=/usr/local/Java/src/jdk-1.3
fi
# rt.jar exists in jdk 1.2 and later.
export JDKBINARIES=${JAVA_HOME}/jre/lib/rt.jar
export JDK_BINARIES=${JDKBINARIES}

export MOCHA_ROOT=${ESCJAVA_ROOT}/mochalib
export MOCHA_CLASSES=${MOCHA_ROOT}/classes

# To get predicate abstraction to work with ESC/Java, you need to download
# jMocha from UC Berkeley.  When you build jMocha, you'll get 3 shared
# objects:  libjbdd.so, libglu.so, libcu.so.  These have to be put in an
# appropriate directory, and LD_LIBRARY_PATH must be set to the name of
# that directory.  For example, if you put the shared objects in
# a directory called ${MOCHA_ROOT}/platform/alpha, then you would include
# the following line here:
# export LD_LIBRARY_PATH=${MOCHA_ROOT}/platform/alpha

######################### classpaths #########################

#
# The classpath for compiling Escjava; no sources outside the repository
# should be on this list:
#

# do not change the number of components here without updating escj!!
export CLASSES=${ESCTOOLS_JARS}/decsrc.jar:${ESCTOOLS_JARS}/mochalib.jar:${ESCTOOLS_JARS}/javafe.jar:${ESCTOOLS_JARS}/escjava.jar:${SRCCLASSDIRECTORY}:${MOCHA_CLASSES}:${CLASSDIRECTORY}

export CLASSPATH=${SOURCEDIRECTORY}:${CLASSES}:.
export ESC_CLASSPATH=${CLASSDIRECTORY}:${ESCTOOLS_JARS}/decsrc.jar:${ESCTOOLS_JARS}/mochalib.jar:${ESCTOOLS_JARS}/javafe.jar:${ESCTOOLS_JARS}/escjava.jar:${JDK_BINARIES}:${JDK_SOURCES}:${MOCHA_CLASSES}
# javadepend needs a classpath where all the sources are in the current dir:
export LCLASSPATH=.:${CLASSES}

#
# The appropriate -bootclasspath for escjava:
#
# Need to sources here because we can't read binary inner classes; need
# the binaries because don't have source for sun.* classes...
#
export JDKSPEC=${JDKSPEC_ROOT}
export BOOTCLASSPATH=${JDKSPEC}:${JDKBINARIES}

alias jls="jls    -bootclasspath ${BOOTCLASSPATH} -E"
alias jwhich="jwhich -bootclasspath ${BOOTCLASSPATH} -X.spec"

#
# The classpath for checking escjava itself (e.g., escself's classpath),
# not counting -bootclasspath:
#
export ESCSPEC=${SOURCEDIRECTORY}:${JAVAFE_ROOT}/java:${SRCDIRECTORY}:${MOCHA_CLASSES}

######################### java* cmds #########################

#
# which version of java:
#
export JAVA='java'

#
# Other java* commands:
#
export JAVAC="javac -g"
export JAVADOC="javadoc -J-mx200m"

#
# Aliases to invoke javac with proper arguments for human use:
#
alias javacd="${JAVAC} -d ${CLASSDIRECTORY}"
alias jall="javacd *.java"

######################### esc* cmds #########################

# the location of the escj script:
export ESCJ=${ESCJAVA_ROOT}/escj

alias escjava="${ESCJ}"

# run escjava on itself:
alias escself="escjava -classpath ${ESCSPEC}"

# OLD:  escjava annotation wizard
#alias	escwizard	${ESCJAVA_ROOT}/escwiz
#alias	escwizardself	${ESCJAVA_ROOT}/escwiz -classpath ${ESCSPEC}

######################### misc cmds #########################

alias copyloaded="${ESCJAVA_ROOT}/java/houdini/copyloaded"
