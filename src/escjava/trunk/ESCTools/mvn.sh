# Distribution script for Maven builds

echo $USER $HOSTNAME $PWD
export MAVEN="cd ESCJava2; ./maven.local"
export REMOTE_TEST="sudo -u dcochran ssh -f"
echo $REMOTE_TEST server $MAVEN
$REMOTE_TEST dcochran@arrow.ucd.ie $MAVEN $* 
$REMOTE_TEST dcochran@object.ucd.ie $MAVEN $* 
$REMOTE_TEST dermotcochran@voting.ucd.ie $MAVEN $* 
