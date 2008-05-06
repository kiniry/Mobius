#!/bin/bash
# Update the test scripts and authorisations
pushd ~/test
svn cleanup
svn update
cp authprogs.conf ~/.ssh
popd