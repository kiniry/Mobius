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

export CLASSDIRECTORY=${JAVAFE_ROOT}/classfiles
export SOURCEDIRECTORY=${JAVAFE_ROOT}/java
export JAVADOCDIRECTORY=${JAVAFE_ROOT}/doc/javadoc

export JDKBINARIES=/usr/java/jdk-1.1/lib/classes.zip

######################### classpaths #########################

#
# The classpath for compiling Javafe; no sources outside the repository
# should be on this list:
#

export CLASSES=${CLASSDIRECTORY}
export DECSRCLIBRARY=${JAVAFE_ROOT}/decsrclib

export CLASSPATH=${SOURCEDIRECTORY}:${CLASSES}:${DECSRCLIBRARY}
# javadepend needs a classpath where all the sources are in the current dir:
export LCLASSPATH=.:${CLASSES}


######################### java* cmds #########################

#
# which version of java:
#

unset JAVAVERSION
#setenv	 JAVAVERSION	1.0.2
export JAVA=java

#
# Other java* commands:
#
export JAVAC=javac
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
