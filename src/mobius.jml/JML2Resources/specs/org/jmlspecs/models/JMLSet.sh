#! /bin/sh
# @(#)$Id: JMLSet.sh,v 1.17 2004/07/22 16:19:02 kui_dai Exp $

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


val_sed()
{
  sed -e ' s/_Elem_/Value/g
	   s/_ElemType_English_/value/g
	   s/_ElemType_/JMLType/g
	   s/_ExtendsSuperClass_/extends JMLValueSetSpecs/g
	   s/_SuperType_/JMLValueType/g
	   s/_SeeSuperClass_/@see JMLValueSetSpecs/g
	   s/_SeeOtherType_/@see JMLEqualsSet\
 * @see JMLObjectSet/g
	   s/_SeeEnumerator_/@see JMLValueSetEnumerator/g
	   s/ _elem_equality_ /.equals/g
	   s/_elem_equality_/.equals/g
           s/_elemArrayHas_/.hasValueEquals/g
	   s/ _elem_clone_/.clone()/g
           s/_weClone_/clones/
	   s/_elem_downcast_/(JMLType) /g
	   s!_nonNullIfObj_ !!g
	   s!_alsoIfValue_!also!g
           s%_Singleton_Constructor_Spec_End_%\
      @ also\
      @  public model_program {\
      @    JMLType copy = (JMLType)e.clone();\
      @    behavior\
      @      assignable this.*;\
      @      ensures hasObject(copy) \&\& int_size() == 1;\
      @  }%g
           s%_Clone_Body_%if (the_list == null) {\
            //@ assume owner == null;\
            return this;\
        } else {\
            return new JMLValueSet((JMLListValueNode)the_list.clone(),\
                                   size);\
        }%g
	 ' $1 >$2
}

eqls_sed()
{
  sed -e ' s/_Elem_/Equals/g
	   s/_ElemType_English_/object/g
	   s/_ElemType_/Object/g
	   s/_ExtendsSuperClass_ //g
	   s/_SuperType_/JMLObjectType/g
	   s/_SeeSuperClass_//g
	   s%_SeeOtherType_%@see JMLObjectSet\
 * @see JMLValueSet%g
	   s/_SeeEnumerator_/@see JMLEqualsSetEnumerator/g
	   s/ _elem_equality_ /.equals/g
	   s/_elem_equality_/.equals/g
           s/_elemArrayHas_/.hasValueEquals/g
	   s/ _elem_clone_//g
           s/_weClone_/does not clone/
	   s/_elem_downcast_//g
	   s!_nonNullIfObj_ !/*@ non_null @*/ !g
	   s!_alsoIfValue_!!g
           s/_Singleton_Constructor_Spec_End_//g
           s%_Clone_Body_%//@ assume owner == null;\
        return this;%g
	 ' $1 >$2
}

obj_sed()
{
 sed -e ' s/_Elem_/Object/g
	   s/_ElemType_English_/object/g
	   s/_ElemType_/Object/g
	   s/_ExtendsSuperClass_ //g
	   s/_SuperType_/JMLObjectType/g
	   s/_SeeSuperClass_//g
	   s/_SeeOtherType_/@see JMLEqualsSet\
 * @see JMLValueSet/g
	   s/_SeeEnumerator_/@see JMLObjectSetEnumerator/g
	   s/_elem_equality_ (\([^()]*\))/== \1/g
	   s/_elem_equality_/==/g
           s/_elemArrayHas_/.hasObjectIdentity/g
	   s/_elem_clone_//g
           s/_weClone_/does not clone/
	   s/_elem_downcast_//g
	   s!_nonNullIfObj_ !/*@ non_null @*/ !g
	   s!_alsoIfValue_!!g
           s/_Singleton_Constructor_Spec_End_//g
           s%_Clone_Body_%//@ assume owner == null;\
        return this;%g
	 ' $1 >$2
}

create_val_set()
{
  echo "Creating JMLValueSet.${SFX1}"
  val_sed JMLSet.${SFX1}-generic JMLValueSet.${SFX1}
  echo "Creating JMLValueSetEnumerator.${SFX1}"
  val_sed JMLSetEnumerator.${SFX1}-generic JMLValueSetEnumerator.${SFX1}
}

create_eqls_set()
{
  echo "Creating JMLEqualsSet.${SFX1}"
  eqls_sed JMLSet.${SFX1}-generic JMLEqualsSet.${SFX1}
  echo "Creating JMLEqualsSetEnumerator.${SFX1}"
  eqls_sed JMLSetEnumerator.${SFX1}-generic JMLEqualsSetEnumerator.${SFX1}
}

create_obj_set()
{
  echo "Creating JMLObjectSet.${SFX1}"
  obj_sed JMLSet.${SFX1}-generic JMLObjectSet.${SFX1}
  echo "Creating JMLObjectSetEnumerator.${SFX1}"
  obj_sed JMLSetEnumerator.${SFX1}-generic JMLObjectSetEnumerator.${SFX1}
}

print_usage()
{
  echo "Usage:  JMLSet  option1 option2" >&2
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
    create_val_set
    create_eqls_set
    create_obj_set
  else
    print_usage
  fi

elif [ "$1" = value ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    create_val_set
  else
    print_usage
  fi

elif [ "$1" = equals ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    create_eqls_set
  else
    print_usage
  fi

elif [ "$1" = object ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    create_obj_set
  else
    print_usage
  fi

else
  print_usage

fi
