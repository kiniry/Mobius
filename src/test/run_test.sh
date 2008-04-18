# move to working directory, get latest and setup for maven tests
echo $HOSTNAME
cd ESCTools
svn up
make pre-maven
mvn $*
