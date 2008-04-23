#/bin/bash
#
# move to local hard link of the working directory
export M2_HOME=/Network/Servers/kind.ucd.ie/Volumes/Home/maven/apache-maven-2.0.8
export MAVEN_OPTS="-Xmx1740m -Xms512m"
echo $HOSTNAME
cd arrow/working-directory
$M2_HOME/bin/mvn $*