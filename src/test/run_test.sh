# move to working directory, get latest and setup for maven tests
echo $HOSTNAME
export MAVEN_OPTS="-Xmx1024 -Xms512"
cd ESCTools
svn cleanup
svn update
make pre-maven
mvn $*