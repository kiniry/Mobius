#! /bin/sh
# @(#)$Id: JMLSequence.sh,v 1.16 2004/07/30 19:10:34 kui_dai Exp $

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
	   s/_ExtendsSuperClass_/extends JMLValueSequenceSpecs/g
	   s/_SuperType_/JMLValueType/g
	   s/_SeeSuperClass_/@see JMLValueSequenceSpecs/g
	   s/_SeeOtherType_/@see JMLObjectSequence/g
	   s/_SeeEnumerator_/@see JMLValueSequenceEnumerator/g
	   s/ _elem_equality_ /.equals/g
	   s/_elem_equality_/.equals/g
	   s/ _elem_clone_/.clone()/g
           s/_weClone_/clones/
	   s/_elem_downcast_/(JMLType) /g
	   s!_nonNullIfObj_ !!g
	   s!_alsoIfValue_!also!g
	   s!_resultGreater0IfObj_!!g
           s%_Singleton_Constructor_Spec_End_%\
      @ also\
      @  public model_program {\
      @    JMLType copy = (JMLType)e.clone();\
      @    behavior\
      @      assignable this.*;\
      @      ensures objectAt(0) == copy \&\& int_length() == 1;\
      @  }%g
           s%_Clone_Body_%if (theSeq == null) {\
            return this;\
        } else {\
            return new JMLValueSequence((JMLListValueNode)theSeq.clone(),\
                                        int_length());\
        }%g
	 ' $1 >$2
}

eqls_sed()
{
 sed -e ' s/_Elem_/Equals/g
	   s/_ElemsAreObjects_/true/g
	   s/_ElemType_English_/object/g
	   s/_ElemType_/Object/g
	   s/_ExtendsSuperClass_ //g
	   s/_SuperType_/JMLObjectType/g
	   s/_SeeSuperClass_//g
	   s/_SeeOtherType_/@see JMLObjectSequence\
 * @see JMLValueSequence/g
	   s/_SeeEnumerator_/@see JMLEqualsSequenceEnumerator/g
	   s/_elem_equality_ /.equals/g
	   s/_elem_equality_/.equals/g
	   s/_elem_clone_//g
           s/_weClone_/does not clone/
	   s/_elem_downcast_//g
	   s!_nonNullIfObj_ !/*@ non_null @*/ !g
	   s!_alsoIfValue_!!g
	   s!_resultGreater0IfObj_!\
     //@ implies_that\
     //@    ensures \\result >= 0;!g
           s/_Singleton_Constructor_Spec_End_//g
           s%_Clone_Body_%return this;%g
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
	   s/_SeeSuperClass_//g
	   s/_SeeOtherType_/@see JMLValueSequence/g
	   s/_SeeEnumerator_/@see JMLObjectSequenceEnumerator/g
	   s/_elem_equality_ (\([^()]*\))/== \1/g
	   s/_elem_equality_/==/g
	   s/_elem_clone_//g
           s/_weClone_/does not clone/
	   s/_elem_downcast_//g
	   s!_nonNullIfObj_ !/*@ non_null @*/ !g
	   s!_alsoIfValue_!!g
	   s!_resultGreater0IfObj_!\
     //@ implies_that\
     //@    ensures \\result >= 0;!g
           s/_Singleton_Constructor_Spec_End_//g
           s%_Clone_Body_%return this;%g
	 ' $1 >$2
}

create_val_seq()
{
  echo "Creating JMLValueSequence.${SFX1}${SFX2}"
  val_sed JMLSequence.${SFX1}-generic JMLValueSequence.${SFX1}${SFX2}
  echo "Creating JMLValueSequenceEnumerator.${SFX1}${SFX2}"
  val_sed JMLSequenceEnumerator.${SFX1}-generic JMLValueSequenceEnumerator.${SFX1}${SFX2}
}

create_eqls_seq()
{
  echo "Creating JMLEqualsSequence.${SFX1}${SFX2}"
  eqls_sed JMLSequence.${SFX1}-generic JMLEqualsSequence.${SFX1}${SFX2}
  echo "Creating JMLEqualsSequenceEnumerator.${SFX1}${SFX2}"
  eqls_sed JMLSequenceEnumerator.${SFX1}-generic JMLEqualsSequenceEnumerator.${SFX1}${SFX2}
}

create_obj_seq()
{
  echo "Creating JMLObjectSequence.${SFX1}${SFX2}"
  obj_sed JMLSequence.${SFX1}-generic JMLObjectSequence.${SFX1}${SFX2}
  echo "Creating JMLObjectSequenceEnumerator.${SFX1}${SFX2}"
  obj_sed JMLSequenceEnumerator.${SFX1}-generic JMLObjectSequenceEnumerator.${SFX1}${SFX2}
}

print_usage()
{
  echo "Usage:  JMLSequence  option1 option2" >&2
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
    create_val_seq
    create_eqls_seq
    create_obj_seq
  else
    print_usage
  fi

elif [ "$1" = value ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    SFX2=
    create_val_seq
  else
    print_usage
  fi

elif [ "$1" = equals ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    SFX2=
    create_eqls_seq
  else
    print_usage
  fi

elif [ "$1" = object ]
then
  if [ "$2" = java -o "$2" = all ]
  then
    SFX1="java"
    SFX2=
    create_obj_seq
  else
    print_usage
  fi

else
  print_usage

fi
