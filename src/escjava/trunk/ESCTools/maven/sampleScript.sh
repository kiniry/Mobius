#/bin/bash
export M2_HOME=/Network/Servers/kind.ucd.ie/Volumes/Home/dcochran/apache-maven-2.0.8
export M2=$M2_HOME/bin
export MAVEN_OPTS=-Xms256m
export JAVA_HOME=/usr
export PATH=$M2:$JAVA_HOME/bin:$PATH
mvn --version 
mvn $*
