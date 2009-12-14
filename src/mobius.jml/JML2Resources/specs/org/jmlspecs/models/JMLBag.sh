#! /bin/sh
# @(#)$Id: JMLBag.sh,v 1.16 2004/07/22 16:19:02 kui_dai Exp $

# Copyright (C) 1998, 1999, 2002 Iowa State University

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
	   s/_ExtendsSuperClass_/extends JMLValueBagSpecs/g
	   s/_SuperType_/JMLValueType/g
	   s/_SeeSuperClass_/@see JMLValueBagSpecs/g
	   s/_SeeOtherType_/@see JMLObjectBag/g
	   s/_SeeEnumerator_/@see JMLValueBagEnumerator/g
	   s/ _elem_equality_ /.equals/g
	   s/_elem_equality_/.equals/g
           s/_elemArrayCount_/.valueEqualsCount/g
	   s/ _elem_clone_/.clone()/g
           s/_weClone_/clones/
	   s/_elem_downcast_/(JMLType) /g
	   s!_nonNullIfObj_ !!g
	   s!_alsoIfValue_!also!g
	   s!_resultGreater0IfObj_!!g
           s!_signalsIllegalWhenCntLT0IfObj_!!g
           s%_Singleton_Constructor_Spec_End_%\
      @ also\
      @  public model_program {\
      @    JMLType copy = (JMLType)elem.clone();\
      @    behavior\
      @      assignable this.*;\
      @      ensures countObject(copy) == 1 \&\& int_size() == 1;\
      @  }%g
           s%_Clone_Body_%if (the_list == null) {\
            //@ assume owner == null;\
            return this;\
        } else {\
            return new JMLValueBag((JMLValueBagEntryNode)the_list.clone(),\
                                   size);\
        }%g
           s%_Clone_Entry_Body_%return new JMLValueBagEntry(theElem == null ? null\
                                     : (JMLType)theElem.clone(),\
                                     count);%g

	 ' $1 >$2
}

eqls_sed()
{
  sed -e ' s/_Elem_/Equals/g
	   s/_ElemsAreObjects_/true/g
	   s/_ElemType_English_/object/g
	   s/_ElemType_/Object/g
	   s/_ExtendsSuperClass_//g
	   s/_SuperType_/JMLObjectType/g
	   s/_SeeSuperClass_//g
	   s/_SeeOtherType_/@see JMLObjectBag\
     * @see JMLValueBag/g
	   s/_SeeEnumerator_/@see JMLEqualsBagEnumerator/g
	   s/ _elem_equality_ /.equals/g
	   s/_elem_equality_/.equals/g
           s/_elemArrayCount_/.valueEqualsCount/g
	   s/ _elem_clone_//g
           s/_weClone_/does not clone/
	   s/_elem_downcast_//g
	   s!_nonNullIfObj_ !/*@ non_null @*/ !g
	   s!_alsoIfValue_!!g
	   s!_resultGreater0IfObj_!\
     //@ implies_that\
     //@    ensures \\result >= 0;!g
           s!_signalsIllegalWhenCntLT0IfObj_!\
    //@ also\
    //@      signals (IllegalArgumentException) cnt < 0;!g
           s/_Singleton_Constructor_Spec_End_//g
           s%_Clone_Body_%return this;%g
           s%_Clone_Entry_Body_%//@ assume owner == null;\
        return this;%g
	 ' $1 >$2
}

obj_sed()
{
 sed -e ' s/_Elem_/Object/g
	   s/_ElemsAreObjects_/true/g
	   s/_ElemType_English_/object/g
	   s/_ElemType_/Object/g
	   s/_ExtendsSuperClass_ //g
	   s/_SuperType_/JMLObjectType/g
	   s/_SeeOtherType_/@see JMLValueSet/g
	   s/_SeeSuperClass_//g
	   s/_SeeEnumerator_/@see JMLObjectSetEnumerator/g
	   s/_elem_equality_ (\([^()]*\))/== \1/g
	   s/_elem_equality_/==/g
           s/_elemArrayCount_/.objectIdentityCount/g
	   s/_elem_clone_//g
           s/_weClone_/does not clone/
	   s/_elem_downcast_//g
	   s!_nonNullIfObj_ !/*@ non_null @*/ !g
	   s!_alsoIfValue_!!g
	   s!_resultGreater0IfObj_!\
     //@ implies_that\
     //@    ensures \\result >= 0;!g
           s!_signalsIllegalWhenCntLT0IfObj_!\
    //@ also\
    //@      signals (IllegalArgumentException) cnt < 0;!g
           s/_Singleton_Constructor_Spec_End_//g
           s%_Clone_Body_%return this;%g
           s%_Clone_Entry_Body_%//@ assume owner == null;\
        return this;%g
	 ' $1 >$2
}

create_val_bag()
{
  echo "Creating JMLValueBag.${SFX1}"
  val_sed JMLBag.${SFX1}-generic JMLValueBag.${SFX1}
  echo "Creating JMLValueBagEnumerator.${SFX1}"
  val_sed JMLBagEnumerator.${SFX1}-generic JMLValueBagEnumerator.${SFX1}
}

create_eqls_bag()
{
  echo "Creating JMLEqualsBag.${SFX1}"
  eqls_sed JMLBag.${SFX1}-generic JMLEqualsBag.${SFX1}
  echo "Creating JMLEqualsBagEnumerator.${SFX1}"
  eqls_sed JMLBagEnumerator.${SFX1}-generic JMLEqualsBagEnumerator.${SFX1}
}

create_obj_bag()
{
  echo "Creating JMLObjectBag.${SFX1}"
  obj_sed JMLBag.${SFX1}-generic JMLObjectBag.${SFX1}
  echo "Creating JMLObjectBagEnumerator.${SFX1}"
  obj_sed JMLBagEnumerator.${SFX1}-generic JMLObjectBagEnumerator.${SFX1}
}

print_usage()
{
  echo "Usage:  JMLBag  option1 option2" >&2
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
    create_val_bag
    create_eqls_bag
    create_obj_bag
  else
    print_usage
  fi

elif [ "$1" = value ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    create_val_bag
  else
    print_usage
  fi

elif [ "$1" = equals ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    create_eqls_bag
  else
    print_usage
  fi

elif [ "$1" = object ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    create_obj_bag
  else
    print_usage
  fi

else
  print_usage

fi
