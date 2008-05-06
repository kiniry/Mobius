#!/bin/bash
# Update the test scripts and authorisations
export WORKDIR=$PWD
cd ~/test
svn cleanup
svn update
cp authprogs.conf ~/.ssh
cd $WORKDIR