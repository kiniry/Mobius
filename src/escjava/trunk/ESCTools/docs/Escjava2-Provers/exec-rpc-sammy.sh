#/bin/bash

# You have to modify this variable :
# Notice that this path contains the name of the binary file at the end!!
sammy="/home/smelc/dpllt-xmlrpc/cvcl/smt/sammy"

if [ ! -x "$sammy" ]
then
    echo $sammy 
    echo "This file does not exist or is not execuable"
    echo "You have to modify this script to set the path to sammy"
else

    make 

    pid_sammy=$(ps -A | grep sammy | cut -f 1 -d " ")
    
    if [ -n "$pid_sammy" ]
	then
	echo "killing previous sammy, pid was "$pid_sammy
	kill $pid_sammy
    fi
    
    echo "starting new sammy instance..."
    ($sammy) &

    java -enableassertions mainRpcSammy
fi
