/* Copyright 2000, 2001, Compaq Computer Corporation */

/*
 * File: TypeModifierPragmaVec.java <p>
 *
 * This file is a template for a vector of X.  It is filled in using
 * sed (e.g, see the Makefile for javafe.ast).  The following
 * replacements need to be done:<p>
 *
 * TypeModifierPragma should be globally replaced with the simple name of the
 *		element type<p>
 * javafe.ast should be globally replaced with the package the resulting
 *		Vector type should live in<p>
 * javafe.ast should be globally replaced with the package the
 *		element type belongs to<p>
 *
 * The resulting type will have name TypeModifierPragmaVec.<p>
 * 
 * Example: to make a vector of java.lang.Integer's that lives in
 * javafe.ast, substitute Integer, javafe.ast, and java.lang
 * respectively.<p>
 *
 *
 * By Default, TypeModifierPragmaVec's may not contain nulls.  If the ability to
 * hold nulls is desired, remove all lines with "// @@@@" on them.<p>
 */




/**
 ** TypeModifierPragmaVec: A Vector of TypeModifierPragma's. <p>
 **
 ** The interface to this class follows java.util.Vector, where
 ** appropriate. <p>
 **
 **
 ** This class was automatically created from the template
 ** javafe.util/_<tt>TYPE</tt>_Vec.j.<p>
 **
 ** DO NOT EDIT!!<p>
 **/

package javafe.ast;


import java.util.Vector;
import javafe.util.StackVector;

import javafe.ast.TypeModifierPragma;


public class  TypeModifierPragmaVec {

    /***************************************************
     *                                                 *
     * Instance fields:				       *
     *                                                 *
     ***************************************************/

    private /*@non_null*/ TypeModifierPragma[] elements;
    //@ invariant (\forall int i; (0<=i && i<count) ==> elements[i]!=null) // @@@@
    //@ invariant \typeof(elements) == \type(TypeModifierPragma[])

    //@ invariant elements.owner == this

    /*@spec_public*/ private int count;
    //@ invariant 0 <= count;
    //@ invariant count <= elements.length;


    /***************************************************
     *                                                 *
     * Private constructors:			       *
     *                                                 *
     ***************************************************/

    //@ requires els!=null
    //@ requires \nonnullelements(els)				// @@@@
    //@ ensures count == els.length
    private TypeModifierPragmaVec(TypeModifierPragma[] els) {
	this.count = els.length;
	this.elements = new TypeModifierPragma[count];
	//@ set elements.owner = this

	System.arraycopy(els,0, elements,0, count);
    }

    //@ requires cnt >= 0
    //@ ensures this.elements.length >= cnt
    private TypeModifierPragmaVec(int cnt) {
	this.elements = new TypeModifierPragma[(cnt == 0 ? 2 : cnt)];
	//@ set elements.owner = this

	this.count = 0;
    }


    /***************************************************
     *                                                 *
     * Public maker methods:			       *
     *                                                 *
     ***************************************************/

    //@ ensures \result!=null
    public static TypeModifierPragmaVec make() { 
	return new TypeModifierPragmaVec(0);
    }

    //@ requires count >= 0
    //@ ensures \result!=null
    public static TypeModifierPragmaVec make(int count) { 
	return new TypeModifierPragmaVec(count);
    }

    //@ requires vec!=null
    //@ requires vec.elementType <: \type(TypeModifierPragma)
    //@ requires !vec.containsNull
    //@ ensures \result!=null
    public static TypeModifierPragmaVec make(Vector vec) {
	int sz = vec.size();
	TypeModifierPragmaVec result = new TypeModifierPragmaVec(sz);
	result.count = sz;
	vec.copyInto(result.elements);
	return result;
    }

    //@ requires els!=null
    //@ requires \nonnullelements(els)			// @@@@
    //@ ensures \result!=null
    //@ ensures \result.count == els.length
    public static TypeModifierPragmaVec make(TypeModifierPragma[] els) {
	return new TypeModifierPragmaVec(els);
    }

    // These are from pop() on s:
    //@ modifies s.vectorCount
    //@ ensures s.vectorCount == \old(s.vectorCount)-1
    //@ modifies s.elementCount, s.currentStackBottom
    //
    //@ requires s.vectorCount>1
    //@ requires s.elementType <: \type(TypeModifierPragma)
    //@ ensures \result!=null
    //@ ensures \result.count == (\old(s.elementCount) - \old(s.currentStackBottom))
    public static TypeModifierPragmaVec popFromStackVector(/*@non_null*/ StackVector s) {
	// Creates a new TypeModifierPragmaVec from top stuff in StackVector
	int sz = s.size();
	TypeModifierPragmaVec r = new TypeModifierPragmaVec(sz);
	s.copyInto(r.elements);
	r.count = sz;
	s.pop();
	return r;
    }


    /***************************************************
     *                                                 *
     * Other methods:				       *
     *                                                 *
     ***************************************************/

    //@ requires 0<=index && index<count
    //@ ensures \result!=null					// @@@@
    public final TypeModifierPragma elementAt(int index)
	  /*throws ArrayIndexOutOfBoundsException*/ {
	if (index < 0 || index >= count)
	    throw new ArrayIndexOutOfBoundsException(index);

	javafe.util.Assert.notNull(elements[index]);		// @@@@
	return elements[index];
    }

    //@ requires 0<=index && index<count
    //@ requires x!=null					// @@@@
    public final void setElementAt(TypeModifierPragma x, int  index) 
	/*throws ArrayIndexOutOfBoundsException*/ {
	if (index < 0 || index >= count)
	    throw new ArrayIndexOutOfBoundsException(index);
	elements[index] = x;
    }

    //@ ensures \result==count
    public final int size() { return count; }

    public final String toString() {
	StringBuffer b = new StringBuffer();
	b.append("{TypeModifierPragmaVec");
	for(int i = 0; i < count; i++) {
	    b.append(" ");
	    if (elements[i]==null)
		b.append("null");
	    else
		b.append(elements[i].toString());
	}
	b.append('}');
	return b.toString();
    }

  //@ ensures \result!=null
  //@ ensures \nonnullelements(\result)					// @@@@
  public final TypeModifierPragma[] toArray() {
      int ct = count;
      TypeModifierPragma[] b = new TypeModifierPragma[ ct ];
      for(int i = 0; i < ct; i++) {
	  b[i]=elements[i];
      }
      return b;
  }

  //@ ensures \result!=null
  public final TypeModifierPragmaVec copy() {
    TypeModifierPragmaVec result = new TypeModifierPragmaVec(count);
    result.count = count;
    System.arraycopy(elements,0,result.elements,0,count);
    return result;
  }

  //@ requires x!=null						// @@@@
  public boolean contains(TypeModifierPragma x) {
    for(int i = 0; i < count; i++) {
      if( elements[i] == x ) return true;
    }
    return false;
  }

  //@ requires x!=null						// @@@@
  //@ modifies count
  //@ ensures count==\old(count)+1
  public final void addElement(TypeModifierPragma x) {
    if( count == elements.length ) {
      TypeModifierPragma[] newElements = new TypeModifierPragma[ 2*(elements.length==0 ?
					      2 : elements.length) ];
      //@ set newElements.owner = this

      System.arraycopy(elements, 0, newElements, 0, elements.length );
      elements = newElements;
    }
    elements[count++]=x;
  }

  //@ requires x!=null						// @@@@
  //@ modifies count
  public final boolean removeElement(TypeModifierPragma x) {
    for( int i=0; i<count; i++ ) {
      if( elements[i] == x ) {
	  int ct=count;
	for( int j=i+1; j<ct; j++ ) 
	  elements[j-1]=elements[j];
	count--;
	return true;
      }
    }
    return false;
  }

    //@ requires 0<=i && i<count
    //@ modifies count
    public final void removeElementAt(int i) {
	int ct=count;
        for (int j=i+1; j<ct; j++) {
            elements[j-1]=elements[j];
	}	    
        count--;
    }

    //@ requires count>0
    //@ modifies count
    //@ ensures count==\old(count)-1
    //@ ensures \result!=null					// @@@@
    public final TypeModifierPragma pop() {
        count--;
        TypeModifierPragma result = elements[count];
	elements[count] = null;
	return result;
    }


    //@ modifies count
    //@ ensures count==0
    public final void removeAllElements() {
	count = 0;
    }


  //@ requires 0 <= index && index <= this.count
  //@ requires obj!=null					// @@@@
  //@ modifies count
  //@ ensures count==\old(count)+1
  public final void insertElementAt(TypeModifierPragma obj, int index) {
    if( count == elements.length ) {
      TypeModifierPragma[] newElements = new TypeModifierPragma[ 2*(elements.length==0 ?
					      2 : elements.length) ];
      //@ set newElements.owner = this					      
      System.arraycopy(elements, 0, newElements, 0, elements.length );
      elements = newElements;
    }
    int ct=count;
    //@ loop_predicate i!=ct ==> elements[ct] != null, i<= ct
    for( int i=count; i>index; i--) 
      elements[i]=elements[i-1];
    elements[index]=obj;
    count++;
  }

  //@ requires vec!=null
  //@ modifies count
  //@ ensures count==\old(count)+vec.count
  public final void append(TypeModifierPragmaVec vec) {
      //@ loop_predicate count == \old(count)+i, i <= vec.count
    for( int i=0; i<vec.size(); i++)
      addElement( vec.elementAt(i) );
  }
}
