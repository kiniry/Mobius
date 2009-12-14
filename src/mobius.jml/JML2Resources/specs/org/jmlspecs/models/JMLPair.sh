#! /bin/sh
# @(#)$Id: JMLPair.sh,v 1.5 2004/06/01 19:51:43 leavens Exp $

# Copyright (C) 1998, 1999, 2004 Iowa State University

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

Key_ValSed='s/_Key_/Value/g
	   s/_KeyType_/JMLType/g
	   s/_key_initializer_/(JMLType)dv.clone()/g
	   s/_key_equal_to_dv_/key.equals(dv)/g
	   s/_key_equal_to_key_/key.equals(key)/g
	 '

Key_EqlSed='s/_Key_/Equals/g
	   s/_KeyType_/Object/g
	   s/_key_initializer_/dv/g
	   s/_key_equal_to_dv_/key.equals(dv)/g
	   s/_key_equal_to_key_/key.equals(key)/g
	 '

Key_ObjSed='s/_Key_/Object/g
	   s/_KeyType_/Object/g
	   s/_key_initializer_/dv/g
	   s/_key_equal_to_dv_/key == dv/g
	   s/_key_equal_to_key_/key == key/g
	 '

Value_ValSed='s/_Value_/Value/g
	   s/_ValueType_/JMLType/g
	   s/_value_initializer_/(JMLType)rv.clone()/g
	   s/_value_equal_to_value_/value.equals(value)/g
	   s/_value_equal_to_rv_/value.equals(rv)/g
	 '

Value_EqlSed='s/_Value_/Equals/g
	   s/_ValueType_/Object/g
	   s/_value_initializer_/rv/g
	   s/_value_equal_to_value_/value.equals(value)/g
	   s/_value_equal_to_rv_/value.equals(rv)/g
	 '

Value_ObjSed='s/_Value_/Object/g
	   s/_ValueType_/Object/g
	   s/_value_initializer_/rv/g
	   s/_value_equal_to_value_/value == value/g
	   s/_value_equal_to_rv_/value == rv/g
	 '

create_pair()
{
  KEYTYPE=$1
  VALUETYPE=$2
  echo "Creating JML${KEYTYPE}${VALUETYPE}Pair.${SFX1}"

  case "$KEYTYPE" in
      Value)
	  KS="$Key_ValSed"
	  case ${VALUETYPE} in
	      value)
		  ST='s/_SuperType_/JMLValueType/g'
		  ;;
	      *)
		  ST='s/_SuperType_/JMLType/g'
		  ;;
	  esac
	  ;;
      Equals)
	  KS="$Key_EqlSed"
	  ;;
      Object)
	  KS="$Key_ObjSed"
	  ;;
      *)
	  echo "got KEYTYPE of $KEYTYPE" >&2
	  exit 1
	  ;;
  esac

  case "$VALUETYPE" in
      Value)
	  VS="$Value_ValSed"
	  ;;
      Equals)
	  VS="$Value_EqlSed"
	  ;;
      Object)
	  VS="$Value_ObjSed"
	  ;;
      *)
	  echo "got VALUETYPE of $VALUETYPE" >&2
	  exit 1
	  ;;
  esac

  sed -e "$KS" -e "$ST" -e "$VS" JMLPair.${SFX1}-generic > JML${KEYTYPE}${VALUETYPE}Pair.${SFX1}
}

print_usage()
{
  echo "Usage:  JMLPair  option1 option2" >&2
  echo "option1:  one of Value, Equals, Object or all" >&2
  echo "option2:  one of Value, Equals, Object or all" >&2
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
    create_pair $KEYTYPE $VALUETYPE
  done
done
