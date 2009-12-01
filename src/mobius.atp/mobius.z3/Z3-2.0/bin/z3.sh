#!/bin/sh
SCRIPT=$0
Z3_PATH=`echo $SCRIPT | sed "s/\\.sh//"`

ARGS=

for p in "$@"
do
  if [ -e "$p" ]
  then
    p=$(winepath -w "$p")
  else
    p=$(echo "$p" | sed 's/^-/\//')
  fi
  ARGS="$ARGS $p"
done

wine "$Z3_PATH" $ARGS
