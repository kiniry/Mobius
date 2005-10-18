#!/bin/bash
# author : Clement

# this script should be removed and the job should be done in another/nicer way

cd java/escjava/vcGeneration

# as only one file is tested this is not robust if the stupid user
# breaks everything by randomly deleting .java files (and consider he does)
if [ ! -e TBoolImplies.java ]
    then
    ./division-j-file.pl TFunction.j 
fi

# same comment here
if [ ! -e TString.java ]
    then
    ./division-j-file.pl TLiteral.j
fi
    