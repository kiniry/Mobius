#!/bin/bash

###
# Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
# See LICENCE.TXT for details.
###

cd debian/src
if [ -a deb-release.tgz ]; then
  rm deb-release.tgz
fi
fakeroot tar --exclude=".svn" -czf deb-release.tgz usr/ etc/
cd ../..

