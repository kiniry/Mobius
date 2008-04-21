# move to working directory, get latest and setup for maven tests
echo $HOSTNAME
export MAVEN_OPTS=-Xms512m -Xmx1024m
cd ESCTools
svn cleanup
svn update
make pre-maven
mvn $*