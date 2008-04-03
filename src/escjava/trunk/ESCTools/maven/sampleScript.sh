#/bin/bash
export M2_HOME=/usr/local/apache-maven/apache-maven-2.0.8
export M2=$M2_HOME/bin
export MAVEN_OPTS=-Xms256m
export JAVA_HOME=/usr/local/java
export PATH=$M2:$JAVA_HOME/bin:$PATH
mvn --version 
mvn $*
