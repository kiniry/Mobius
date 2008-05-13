#!/bin/bash
#
# Setup hardlinks to the working directory with latest checkout
export M2_HOME=/Network/Servers/kind.ucd.ie/Volumes/Home/maven/apache-maven-2.0.8
export MAVEN_OPTS="-Xmx1740m -Xms512m"
echo "Running on "$HOSTNAME
cd arrow/ESCTOOLS
echo "Getting latest checkout..."
svn up
echo "export ESCTOOLS_ROOT="$PWD > Makefile.local
make pre-maven
echo "Creating hard link trees for other servers in this domain..."
nice ../../test/hardlink.sh ~maven/object/working-directory
nice ../../test/hardlink.sh ~maven/category/working-directory
echo "Running tests..."
$M2_HOME/bin/mvn $*