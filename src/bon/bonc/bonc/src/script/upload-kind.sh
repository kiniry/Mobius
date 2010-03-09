#!/bin/bash

server="kind.ucd.ie"
path="/Volumes/Data/web/kindsoft/html/products/opensource/BONc/releases"

read -p "Enter username on kind:" user

#TODO check for release, and quit with error if none

KINDVER=`wget -qO - http://kind.ucd.ie/products/opensource/BONc/releases/version`
KINDVERDEB=`echo ${KINDVER} | sed -e 's/-/_/'`

LATEST=`cat release/version`

echo "Local version: $LATEST"
echo "Version on server: $KINDVER"

if [[ "$LATEST" != "$KINDVER" ]]; then

  echo "Moving old releases"
  ssh ${user}@${server} "mv ${path}/bonc* ${path}/old-releases"

  echo "Uploading new release files"
  scp release/*.txt release/changelog release/update release/version release/bonc* ${user}@${server}:${path}/
  
  echo "Success!"  
else
  ##TODO prompt if we want to continue
  echo "Already at latest version."
fi





