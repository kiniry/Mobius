#!/bin/bash

version=`cat release/version`
version=`echo $version | sed -e 's/-/_/'`
file="${version}_all.deb"

scp release/$file hunter.ucd.ie:/var/www/bon/apt/incoming

ssh hunter.ucd.ie "sudo reprepro -b /var/www/bon/apt includedeb unstable /var/www/bon/apt/incoming/$file"
 
echo "Version $version"