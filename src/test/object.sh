#/bin/bash
#
# move to local hardlink of working directory and setup for maven tests
export M2_HOME=/Network/Servers/kind.ucd.ie/Volumes/Home/maven/apache-maven-2.0.8
export MAVEN_OPTS="-Xmx1740m -Xms512m"
export JAVA_HOME=/usr/local/java/jdk1.5.0_13/
echo $HOSTNAME
cd object/working-directory
$M2_HOME/bin/mvn $*