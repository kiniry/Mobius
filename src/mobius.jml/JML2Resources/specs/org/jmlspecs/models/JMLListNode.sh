#! /bin/sh
# @(#)$Id: JMLListNode.sh,v 1.6 2004/05/25 22:10:42 leavens Exp $

# Copyright (C) 1998, 1999 Iowa State University

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


val_sed()
{
  sed -e ' s/_Elem_/Value/g
	   s/_ElemsAreObjects_/false/g
	   s/_ElemType_English_/value/g
	   s/_ElemType_/JMLType/g
	   s/_SuperType_/JMLValueType/g
	   s/ _elem_equality_ /.equals/g
	   s/_elem_equality_/.equals/g
	   s/ _elem_clone_/.clone()/g
           s/_weClone_/clones/
           s%_Clone_Body_%// Recall that cons() handles cloning.\
        JMLListValueNode ret = cons(val,\
                                    (next == null ? null\
                                     : (JMLListValueNode) next.clone()));\
        return ret;%g
	 ' $1 >$2
}

eqls_sed()
{
  sed -e ' s/_Elem_/Equals/g
	   s/_ElemsAreObjects_/true/g
	   s/_ElemType_English_/object/g
	   s/_ElemType_/Object/g
	   s/_SuperType_/JMLType/g
	   s/ _elem_equality_ /.equals/g
	   s/_elem_equality_/.equals/g
	   s/_elem_clone_//g
           s/_weClone_/does not clone/
           s%_Clone_Body_%return this;%g
	 ' $1 >$2
}

obj_sed()
{
 sed -e ' s/_Elem_/Object/g
	   s/_ElemsAreObjects_/true/g
	   s/_ElemType_English_/object/g
	   s/_ElemType_/Object/g
	   s/_SuperType_/JMLType/g
	   s/_elem_equality_ (\([^()]*\))/== \1/g
	   s/_elem_equality_/==/g
	   s/_elem_clone_//g
           s/_weClone_/does not clone/
           s%_Clone_Body_%return this;%g
	 ' $1 >$2
}

create_val_list()
{
  echo "Creating JMLListValueNode.${SFX1}${SFX2}"
  val_sed JMLListNode.${SFX1}-generic JMLListValueNode.${SFX1}${SFX2}
}

create_eqls_list()
{
  echo "Creating JMLListEqualsNode.${SFX1}${SFX2}"
  eqls_sed JMLListNode.${SFX1}-generic JMLListEqualsNode.${SFX1}${SFX2}
}

create_obj_list()
{
  echo "Creating JMLListObjectNode.${SFX1}${SFX2}"
  obj_sed JMLListNode.${SFX1}-generic JMLListObjectNode.${SFX1}${SFX2}
}

print_usage()
{
  echo "Usage:  JMLList  option1 option2" >&2
  echo "option1:  one of value, equals, object, all" >&2
  echo "option2:  one of java, all" >&2
  exit 1
} 

if [ "$#" != 2 ]
then
  print_usage

elif [ "$1" = all ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    SFX2=
    create_val_list
    create_eqls_list
    create_obj_list
  else
    print_usage
  fi

elif [ "$1" = value ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    SFX2=
    create_val_list
  else
    print_usage
  fi

elif [ "$1" = equals ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    SFX2=
    create_eqls_list
  else
    print_usage
  fi

elif [ "$1" = object ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    SFX2=
    create_obj_list
  else
    print_usage
  fi

else
  print_usage

fi
