#! /bin/sh
# @(#)$Id: JMLMap.sh,v 1.5 2004/06/01 19:51:43 leavens Exp $

# Copyright (C) 1998, 1999, 2002, 2004 Iowa State University

# This file is part of JML

# JML is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2, or (at your option)
# any later version.

# JML is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.

# You should have received a copy of the GNU General Public License
# along with JML; see the file COPYING.  If not, write to
# the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.


Domain_ValSed='s/_Domain_/Value/g
	   s/_DomainType_/JMLType/g
	 '

Domain_EqlSed='s/_Domain_/Equals/g
	   s/_DomainType_/Object/g
	 '

Domain_ObjSed='s/_Domain_/Object/g
	   s/_DomainType_/Object/g
	 '

Range_ValSed='s/_Range_/Value/g
	   s/_RangeType_/JMLType/g
	   s/_rangeEquals_ /.equals/g
	 '

Range_EqlSed='s/_Range_/Equals/g
	   s/_RangeType_/Object/g
	   s/_rangeEquals_ /.equals/g
	 '

Range_ObjSed='s/_Range_/Object/g
	   s/_RangeType_/Object/g
	   s/_rangeEquals_ / == /g
	 '

create_map()
{
  DOMAINTYPE=$1
  RANGETYPE=$2

  case "$DOMAINTYPE" in
      Value)
	  DS="$Domain_ValSed"
	  ;;
      Equals)
	  DS="$Domain_EqlSed"
	  ;;
      Object)
	  DS="$Domain_ObjSed"
	  ;;
      *)
	  echo "got DOMAINTYPE of $DOMAINTYPE" >&2
	  exit 1
	  ;;
  esac

  case "$RANGETYPE" in
      Value)
	  RS="$Range_ValSed"
	  ;;
      Equals)
	  RS="$Range_EqlSed"
	  ;;
      Object)
	  RS="$Range_ObjSed"
	  ;;
      *)
	  echo "got RANGETYPE of $RANGETYPE" >&2
	  exit 1
	  ;;
  esac

  echo "Creating JML${DOMAINTYPE}To${RANGETYPE}Map.${SFX1}"
  sed -e "$DS" -e "$RS" "JMLMap.${SFX1}-generic" > "JML${DOMAINTYPE}To${RANGETYPE}Map.${SFX1}"
}

print_usage()
{
  echo "Usage: JMLMap option1 option2" >&2
  echo "option1: one of Value, Equals, Object or all" >&2
  echo "option2: one of Value, Equals, Object or all" >&2
  exit 1
} 

if [ "$#" != 2 ]
then
  print_usage
fi

kt="Value Equals Object"
case "$1" in
    Value|value|val)
	kt=Value
	;;
    Equals|equals|eqls)
	kt=Equals
	;;
    Object|object|obj)
	kt=Object
	;;
    all)
	;;
    *)
	print_usage
	;;
esac

vt="Value Equals Object"
case "$2" in
    Value|value|val)
	vt=Value
	;;
    Equals|equals|eqls)
	vt=Equals
	;;
    Object|object|obj)
	vt=Object
	;;
    all)
	;;
    *)
	print_usage
	;;
esac

SFX1="java"
for KEYTYPE in $kt
do
  for VALUETYPE in $vt
  do
    create_map $KEYTYPE $VALUETYPE
  done
done
