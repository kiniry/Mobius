# Copyright 2000, 2001, Compaq Computer Corporation

#
# This file must be sourced before running gnumake anywhere in this
# repository.  Moreover, it must be sourced in the top directory of this
# repository.
#

############################## roots ##############################

export RCC_ROOT=`pwd`
if [ ! -f $RCC_ROOT/setup ]; then
    echo "Error: Must source setup from the directory that contains it"
    exit 1
fi

export JAVAFE_ROOT=$RCC_ROOT/../Javafe


######################### locations #########################

export CLASSDIRECTORY=$RCC_ROOT/classes
export SOURCEDIRECTORY=$RCC_ROOT/java
export JAVADOC_GEN_DIR=$RCC_ROOT/doc/javadoc
export JAVA_HOME=/usr/lib/j2sdk1.4-sun

export DECSRCLIBRARY=$JAVAFE_ROOT/decsrclib

# TODO
# Where to find binaries for the JDK libraries:
#

export JDKBINARIES=$JAVA_HOME/jre/lib/rt.jar


######################### classpaths #########################

#
# The classpath for compiling Escjava; no sources outside the repository
# should be on this list:
#

export JAVAFE=$JAVAFE_ROOT/classfiles
export ESCJAVA=$RCC_ROOT/../Escjava/classfiles/
export CLASSES=$CLASSDIRECTORY:$JAVAFE:$DECSRCLIBRARY:$ESCJAVA

export CLASSPATH=$SOURCEDIRECTORY:$CLASSES
# javadepend needs a classpath where all the sources are in the current dir:
export LCLASSPATH=.:$CLASSES

# TODO: This is probably wrong. Initially it contained "/src/java", whatever that is.
export RCC_CLASSPATH=$CLASSDIRECTORY:$JAVAFE

#
# The appropriate -bootclasspath for escjava:
#
# Need to sources here because we can't read binary inner classes; need
# the binaries because don't have source for sun.* classes...
#
#export JDKSPEC=$JDKSPEC_ROOT
#export BOOTCLASSPATH=$JDKSPEC:$JDKBINARIES
export BOOTCLASSPATH=$JDKBINARIES

######################### java* cmds #########################


#
# which version of java:
#

export JAVA=java
export JAVAC=javac
export JAVADOC=javadoc

#
# Aliases to invoke javac with proper arguments for human use:
#
alias javacd="${JAVAC} -d ${CLASSDIRECTORY}"
alias jall="javacd *.java"

######################### esc* cmds #########################

# the location of the escj script:
export RCC=$RCC_ROOT/rcc
export RCCN=$RCC_ROOT/rccn

alias rcc=$RCC
alias rccn=$RCC_ROOT/rccn 

alias rccw=$RCC_ROOT/java/rccwizard/rccwiz
export RCCW=$RCC_ROOT/java/rccwizard/rccwiz
