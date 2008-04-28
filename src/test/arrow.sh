#/bin/bash
#
# Setup hardlinks to the working directory with latest checkout
export M2_HOME=/Network/Servers/kind.ucd.ie/Volumes/Home/maven/apache-maven-2.0.8
export MAVEN_OPTS="-Xmx1740m -Xms512m"
echo $HOSTNAME
cd arrow/ESCTOOLS
svn up
echo "export ESCTOOLS_ROOT="$WORKDIR > Makefile.local
make pre-maven
nice ../../test/hardlink.sh ~maven/object/working-directory
nice ../../test/hardlink.sh ~maven/category/working-directory
$M2_HOME/bin/mvn $*