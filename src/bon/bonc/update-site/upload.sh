#!/bin/bash

server="kind.ucd.ie"
path="/Volumes/Data/web/kindsoft/html/products/opensource/BONc/update"

read -p "Enter username on kind:" user

scp site.xml logs.zip content.jar artifacts.jar ${user}@${server}:${path}/
scp features/* ${user}@${server}:${path}/features/
scp plugins/* ${user}@${server}:${path}/plugins/