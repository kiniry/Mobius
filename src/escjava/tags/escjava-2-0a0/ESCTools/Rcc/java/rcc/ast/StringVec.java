/*
 * File: StringVec.java <p>
 *
 * This file is a template for a vector of X.  It is filled in using
 * sed (e.g, see the Makefile for javafe.ast).  The following
 * replacements need to be done:<p>
 *
 * String should be globally replaced with the simple name of the
 *		element type<p>
 * rcc.ast should be globally replaced with the package the resulting
 *		Vector type should live in<p>
 * java.lang should be globally replaced with the package the
 *		element type belongs to<p>
 *
 * The resulting type will have name StringVec.<p>
 * 
 * Example: to make a vector of java.lang.Integer's that lives in
 * javafe.ast, substitute Integer, javafe.ast, and java.lang
 * respectively.<p>
 *
 *
 * By Default, StringVec's may not contain nulls.  If the ability to
 * hold nulls is desired, remove all lines with "// @@@@" on them.<p>
 */




/**
 ** StringVec: A Vector of String's. <p>
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

package rcc.ast;


import java.util.Vector;
import javafe.util.StackVector;

import java.lang.String;


public class  StringVec {

    /***************************************************
     *                                                 *
     * Instance fields:				       *
     *                                                 *
     ***************************************************/

    private String[] elements;
    //@ invariant elements!=null
    //@ invariant (forall int i; (0<=i && i<count) ==> elements[i]!=null) // @@@@ //private invariant
    //@ invariant typeof(elements) == type(String[])

    /*@ invariant (forall StringVec s; s==null || s==this //private invariant
			|| s.elements!=elements) */	  //private invariant

    /*@spec_public*/ private int count;
    //@ invariant 0 <= count && count <= elements.length


    /***************************************************
     *                                                 *
     * Private constructors:			       *
     *                                                 *
     ***************************************************/

    //@ requires els!=null
    //@ requires elemsnonnull(els)				// @@@@
    //@ ensures count == els.length
    private StringVec(String[] els) {
	this.count = els.length;
	this.elements = new String[count];
	/*@ assume (forall StringVec s; s==null || s==this
	            || s.elements!=elements) */

	System.arraycopy(els,0, elements,0, count);
    }

    //@ requires cnt >= 0
    //@ ensures this.elements.length >= cnt
    private StringVec(int cnt) {
	this.elements = new String[(cnt == 0 ? 2 : cnt)];
	/*@ assume (forall StringVec s; s==null || s==this
	            || s.elements!=elements) */

	this.count = 0;
    }


    /***************************************************
     *                                                 *
     * Public maker methods:			       *
     *                                                 *
     ***************************************************/

    //@ ensures RES!=null
    public static StringVec make() { 
	return new StringVec(0);
    }

    //@ requires count >= 0
    //@ ensures RES!=null
    public static StringVec make(int count) { 
	return new StringVec(count);
    }

    //@ requires vec!=null
    //@ requires vec.elementType <: type(String)
    //@ requires !vec.containsNull
    //@ ensures RES!=null
    public static StringVec make(Vector vec) {
	int sz = vec.size();
	StringVec result = new StringVec(sz);
	result.count = sz;
	vec.copyInto(result.elements);
	//@ assume (forall int i; (0<=i && i<sz) ==> result.elements[i]!=null)
	return result;
    }

    //@ requires els!=null
    //@ requires elemsnonnull(els)			// @@@@
    //@ ensures RES!=null
    //@ ensures RES.count == els.length
    public static StringVec make(String[] els) {
	return new StringVec(els);
    }

    //@ requires s!=null
    //@ requires s.vectorCount>1
    //@ requires s.elementType <: type(String)
    //@ ensures RES!=null
    public static StringVec popFromStackVector(StackVector s) {
	// Creates a new StringVec from top stuff in StackVector
	int sz = s.size();
	StringVec r = new StringVec(sz);
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
    //@ ensures RES!=null					// @@@@
    public final String elementAt(int index)
	  /*throws ArrayIndexOutOfBoundsException*/ {
	if (index < 0 || index >= count)
	    throw new ArrayIndexOutOfBoundsException(index);

	javafe.util.Assert.notNull(elements[index]);		// @@@@
	return elements[index];
    }

    //@ requires 0<=index && index<count
    //@ requires x!=null					// @@@@
    public final void setElementAt(String x, int  index) 
	/*throws ArrayIndexOutOfBoundsException*/ {
	if (index < 0 || index >= count)
	    throw new ArrayIndexOutOfBoundsException(index);
	elements[index] = x;
    }

    //@ ensures RES==count
    public final int size() { return count; }

    public final String toString() {
	StringBuffer b = new StringBuffer();
	b.append("{StringVec");
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

  //@ ensures RES!=null
  //@ ensures elemsnonnull(RES)					// @@@@
  public final String[] toArray() {
    String[] b = new String[ count ];
    for(int i = 0; i < count; i++) {
        b[i]=elements[i];
    }
    return b;
  }

  //@ ensures RES!=null
  public final StringVec copy() {
    StringVec result = new StringVec(count);
    result.count = count;
    System.arraycopy(elements,0,result.elements,0,count);
    return result;
  }

  //@ requires x!=null						// @@@@
  public boolean contains(String x) {
    for(int i = 0; i < count; i++) {
      if( elements[i] == x ) return true;
    }
    return false;
  }

  //@ requires x!=null						// @@@@
  //@ modifies count
  //@ ensures count==PRE(count)+1
  public final void addElement(String x) {
    if( count == elements.length ) {
      String[] newElements = new String[ 2*(elements.length==0 ?
					      2 : elements.length) ];
      System.arraycopy(elements, 0, newElements, 0, elements.length );
      /*@ assume (forall StringVec s; s==null || s.elements!=newElements) */
      elements = newElements;
    }
    elements[count++]=x;
  }

  //@ requires x!=null						// @@@@
  //@ modifies count
  public final boolean removeElement(String x) {
    for( int i=0; i<count; i++ ) {
      if( elements[i] == x ) {
	for( int j=i+1; j<count; j++ ) 
	  elements[j-1]=elements[j];
	count--;
	return true;
      }
    }
    return false;
  }

  //@ requires count>0
  //@ modifies count
  //@ ensures count==PRE(count)-1
  public final String pop() {
    String t = elements[--count];
    elements[count] = null;
    return t; 
  }


    //@ modifies count
    //@ ensures count==0
    public final void removeAllElements() {
	count = 0;
    }


  //@ requires 0 <= index && index <= this.count
  //@ requires obj!=null					// @@@@
  //@ modifies count
  //@ ensures count==PRE(count)+1
  public final void insertElementAt(String obj, int index) {
    if( count == elements.length ) {
      String[] newElements = new String[ 2*(elements.length==0 ?
					      2 : elements.length) ];
      System.arraycopy(elements, 0, newElements, 0, elements.length );
      /*@ assume (forall StringVec s; s==null || s==this
			|| s.elements!=newElements) */
      elements = newElements;
    }
    for( int i=count; i>index; i--) 
      elements[i]=elements[i-1];
    elements[index]=obj;
    count++;
  }

  //@ requires vec!=null
  //@ modifies count
  //@ ensures count==PRE(count)+vec.count
  public final void append(StringVec vec) { 	//@ nowarn Exception
    for( int i=0; i<vec.size(); i++)
      addElement( vec.elementAt(i) );
  }
}
