#!/bin/bash
# author : Clement

fileAdress=http://apache.mirrors.esat.net/ws/xmlrpc/binaries/xmlrpc-1.2-b1.tar.gz
fileName=xmlrpc-1.2-b1.tar.gz

if [ ! -r "$fileName" ]
    then # get the file

    `wget $fileAdress`

    if [ "$?" -ne 0 ]
	then #if fail, print explications
	
	echo "************"
	echo ""
	echo "Could not get the xml rpc library from apache website : "
	echo $fileAdress
	echo ""
	echo "Please check that you have wget installed, or retrieve this file manually on the adress below and place the .tar.gz file in "$ESCTOOLS_ROOT"Escjava/"
	echo ""
	echo "************"
	exit 1
    fi
fi

# extract the file 
tar -xzf $fileName

if [ ! -e classfiles/org ]
    then

    fileNameShort=xmlrpc-1.2-b1

    jar -xf $fileNameShort/$fileNameShort.jar

    #copy licence
    cp $fileNameShort/LICENSE.txt ./LICENSE-xml-rpc

    echo "This product includes software developed by the Apache Software Foundation
(http://www.apache.org/).  
See the LICENSE-xml-rpc file for the appropriate license 
text.

The source for the Apache XML-RPC library xmlrpc-1.2-b1 may be 
retrieved from the Apache Web Services Project website at: 
http://ws.apache.org/xmlrpc/." > README-xml-rpc

    # move the appropriate files
    
    if [ ! -e classfiles/ ]
	then
	mkdir classfiles/
    fi

    mv org/ classfiles/
    mv uk/ classfiles/

    #clean the rest of the files
    rm -r xmlrpc-1.2-b1 META-INF

    exit 0

fi

exit 0
