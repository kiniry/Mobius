#! /bin/sh
# @(#)$Id: JMLRelation.sh,v 1.4 2004/06/01 19:51:43 leavens Exp $

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
	   s/_val_not_equal_to_dv_/!val.equals(dv)/g
	 '

Domain_EqlSed='s/_Domain_/Equals/g
	   s/_DomainType_/Object/g
	   s/_val_not_equal_to_dv_/!val.equals(dv)/g
	 '

Domain_ObjSed='s/_Domain_/Object/g
	   s/_DomainType_/Object/g
	   s/_val_not_equal_to_dv_/val != dv/g
	 '

Range_ValSed='s/_Range_/Value/g
	   s/_RangeType_/JMLType/g
	   s/_r_not_equal_to_rv_/!r.equals(rv)/g
	 '

Range_EqlSed='s/_Range_/Equals/g
	   s/_RangeType_/Object/g
	   s/_r_not_equal_to_rv_/!r.equals(rv)/g
	 '

Range_ObjSed='s/_Range_/Object/g
	   s/_RangeType_/Object/g
	   s/_r_not_equal_to_rv_/r != rv/g
	 '

create_rel()
{
  DOMAINTYPE=$2
  RANGETYPE=$3

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

  for k in $1
  do
    echo "Creating JML${DOMAINTYPE}To${RANGETYPE}${k}.${SFX1}"
    sed -e "$DS" -e "$RS" "JML${k}.${SFX1}-generic" > "JML${DOMAINTYPE}To${RANGETYPE}${k}.${SFX1}"
  done
}

print_usage()
{
  echo "Usage: JMLRelation kind option1 option2" >&2
  echo "kind: one of Relation RelationEnumerator RelationImageEnumerator or all" >&2
  echo "option1: one of Value, Equals, Object or all" >&2
  echo "option2: one of Value, Equals, Object or all" >&2
  exit 1
} 

if [ "$#" != 3 ]
then
  print_usage
fi

kind="Relation RelationEnumerator RelationImageEnumerator"
case "$1" in
    Relation)
	kind=Relation
	;;
    RelationEnumerator)
	kind=RelationEnumerator
	;;
    RelationImageEnumerator)
	kind=RelationImageEnumerator
	;;
    all)
	;;
    *)
	print_usage
	;;
esac

kt="Value Equals Object"
case "$2" in
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
case "$3" in
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
    create_rel "$kind" $KEYTYPE $VALUETYPE
  done
done
