#!/bin/bash

server="kind.ucd.ie"
path="/Volumes/Data/web/kindsoft/html/products/opensource/BONc/update"

read -p "Enter username on kind:" user

#Remove existing content first?
scp site.xml logs.zip content.jar artifacts.jar ${user}@${server}:${path}/
scp -r features ${user}@${server}:${path}/
scp -r plugins ${user}@${server}:${path}/
scp -r web ${user}@${server}:${path}/

echo "Done."