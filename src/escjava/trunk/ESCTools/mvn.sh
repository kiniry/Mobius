# Distribution script for Maven builds

echo $USER $HOSTNAME $PWD
export COMMAND = "cd ESCJava2; mvn"
ssh arrow.ucd.ie $COMMAND $*
ssh object.ucd.ie $COMMAND $*
ssh morphism.ucd.ie $COMMAND $*
ssh category.ucd.ie $COMMAND $*
ssh voting.ucd.ie $COMMAND $*
