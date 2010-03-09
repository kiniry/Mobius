#!/bin/bash

#Find the latest version and the corresponding .deb file name
version=`cat release/version | sed -e 's/-/_/'`
file="${version}_all.deb"

#Copy the file to the server
scp release/$file hunter.ucd.ie:/var/www/bon/apt/incoming

#Execute reprepro on the server to include it in the apt repository
ssh hunter.ucd.ie "sudo reprepro -b /var/www/bon/apt includedeb unstable /var/www/bon/apt/incoming/$file"

echo "Done"