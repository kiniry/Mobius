#!/bin/bash

###
# Copyright (c) 2007, Fintan Fairmichael, University College Dublin under the BSD licence.
# See LICENCE.TXT for details.
###

if [ $1 ]; then
	cd dist
	tar -czf ../release/$1.tar.gz *
	tar -cjf ../release/$1.tar.bz2 *
	zip -r ../release/$1.zip *
fi
