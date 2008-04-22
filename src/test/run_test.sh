# move to working directory, get latest and setup for maven tests
echo $HOSTNAME
export MAVEN_OPTS="-Xmx1740m -Xms512m"
cd ESCTools
svn cleanup
svn update
make pre-maven
mvn $*