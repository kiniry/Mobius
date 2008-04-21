# move to working directory, get latest and setup for maven tests
echo $HOSTNAME
cd ESCTools
svn cleanup
svn update
make pre-maven
mvn $*