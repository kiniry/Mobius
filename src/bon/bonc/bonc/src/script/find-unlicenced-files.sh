#!/bin/bash

find src/ -type f | grep -v ".svn" | grep -v ".tokens" | grep -v "__.g" >> temp1
cat temp1 | xargs grep -l "LICENCE.TXT" >> temp2

diff temp1 temp2

rm temp1
rm temp2
cd ..
