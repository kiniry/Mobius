#/bin/bash
#
# move to working directory, get latest and setup for maven tests
export M2_HOME=/Network/Servers/kind.ucd.ie/Volumes/Home/maven/apache-maven-2.0.8
export MAVEN_OPTS="-Xmx1024 -Xms512"
echo $HOSTNAME
cd object/ESCTools
echo "export ESCTOOLS_ROOT="$PWD > Makefile.local
svn cleanup
svn update
make pre-maven
$M2_HOME/bin/mvn $*