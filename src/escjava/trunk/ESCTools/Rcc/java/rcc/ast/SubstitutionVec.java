/*
 * File: SubstitutionVec.java <p>
 *
 * This file is a template for a vector of X.  It is filled in using
 * sed (e.g, see the Makefile for javafe.ast).  The following
 * replacements need to be done:<p>
 *
 * Substitution should be globally replaced with the simple name of the
 *                element type<p>
 * rcc.ast should be globally replaced with the package the resulting
 *                Vector type should live in<p>
 * rcc.ast should be globally replaced with the package the
 *                element type belongs to<p>
 *
 * The resulting type will have name SubstitutionVec.<p>
 * 
 * Example: to make a vector of java.lang.Integer's that lives in
 * javafe.ast, substitute Integer, javafe.ast, and java.lang
 * respectively.<p>
 *
 *
 * By Default, SubstitutionVec's may not contain nulls.  If the ability to
 * hold nulls is desired, remove all lines with "// @@@@" on them.<p>
 */




/**
 ** SubstitutionVec: A Vector of Substitution's. <p>
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

import rcc.ast.Substitution;


public class  SubstitutionVec {

    /***************************************************
     *                                                 *
     * Instance fields:                                       *
     *                                                 *
     ***************************************************/

    private Substitution[] elements;
    //@ invariant elements!=null
    //@ invariant (forall int i; (0<=i && i<count) ==> elements[i]!=null) // @@@@ //private invariant
    //@ invariant typeof(elements) == type(Substitution[])

    /*@ invariant (forall SubstitutionVec s; s==null || s==this //private invariant
                        || s.elements!=elements) */          //private invariant

    /*@spec_public*/ private int count;
    //@ invariant 0 <= count && count <= elements.length


    /***************************************************
     *                                                 *
     * Private constructors:                               *
     *                                                 *
     ***************************************************/

    //@ requires els!=null
    //@ requires elemsnonnull(els)                                // @@@@
    //@ ensures count == els.length
    private SubstitutionVec(Substitution[] els) {
        this.count = els.length;
        this.elements = new Substitution[count];
        /*@ assume (forall SubstitutionVec s; s==null || s==this
                    || s.elements!=elements) */

        System.arraycopy(els,0, elements,0, count);
    }

    //@ requires cnt >= 0
    //@ ensures this.elements.length >= cnt
    private SubstitutionVec(int cnt) {
        this.elements = new Substitution[(cnt == 0 ? 2 : cnt)];
        /*@ assume (forall SubstitutionVec s; s==null || s==this
                    || s.elements!=elements) */

        this.count = 0;
    }


    /***************************************************
     *                                                 *
     * Public maker methods:                               *
     *                                                 *
     ***************************************************/

    //@ ensures RES!=null
    public static SubstitutionVec make() { 
        return new SubstitutionVec(0);
    }

    //@ requires count >= 0
    //@ ensures RES!=null
    public static SubstitutionVec make(int count) { 
        return new SubstitutionVec(count);
    }

    //@ requires vec!=null
    //@ requires vec.elementType <: type(Substitution)
    //@ requires !vec.containsNull
    //@ ensures RES!=null
    public static SubstitutionVec make(Vector vec) {
        int sz = vec.size();
        SubstitutionVec result = new SubstitutionVec(sz);
        result.count = sz;
        vec.copyInto(result.elements);
        //@ assume (forall int i; (0<=i && i<sz) ==> result.elements[i]!=null)
        return result;
    }

    //@ requires els!=null
    //@ requires elemsnonnull(els)                        // @@@@
    //@ ensures RES!=null
    //@ ensures RES.count == els.length
    public static SubstitutionVec make(Substitution[] els) {
        return new SubstitutionVec(els);
    }

    //@ requires s!=null
    //@ requires s.vectorCount>1
    //@ requires s.elementType <: type(Substitution)
    //@ ensures RES!=null
    public static SubstitutionVec popFromStackVector(StackVector s) {
        // Creates a new SubstitutionVec from top stuff in StackVector
        int sz = s.size();
        SubstitutionVec r = new SubstitutionVec(sz);
        s.copyInto(r.elements);
        r.count = sz;
        s.pop();
        return r;
    }


    /***************************************************
     *                                                 *
     * Other methods:                                       *
     *                                                 *
     ***************************************************/

    //@ requires 0<=index && index<count
    //@ ensures RES!=null                                        // @@@@
    public final Substitution elementAt(int index)
          /*throws ArrayIndexOutOfBoundsException*/ {
        if (index < 0 || index >= count)
            throw new ArrayIndexOutOfBoundsException(index);

        javafe.util.Assert.notNull(elements[index]);                // @@@@
        return elements[index];
    }

    //@ requires 0<=index && index<count
    //@ requires x!=null                                        // @@@@
    public final void setElementAt(Substitution x, int  index) 
        /*throws ArrayIndexOutOfBoundsException*/ {
        if (index < 0 || index >= count)
            throw new ArrayIndexOutOfBoundsException(index);
        elements[index] = x;
    }

    //@ ensures RES==count
    public final int size() { return count; }

    public final String toString() {
        StringBuffer b = new StringBuffer();
        b.append("{SubstitutionVec");
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
  //@ ensures elemsnonnull(RES)                                        // @@@@
  public final Substitution[] toArray() {
    Substitution[] b = new Substitution[ count ];
    for(int i = 0; i < count; i++) {
        b[i]=elements[i];
    }
    return b;
  }

  //@ ensures RES!=null
  public final SubstitutionVec copy() {
    SubstitutionVec result = new SubstitutionVec(count);
    result.count = count;
    System.arraycopy(elements,0,result.elements,0,count);
    return result;
  }

  //@ requires x!=null                                                // @@@@
  public boolean contains(Substitution x) {
    for(int i = 0; i < count; i++) {
      if( elements[i] == x ) return true;
    }
    return false;
  }

  //@ requires x!=null                                                // @@@@
  //@ modifies count
  //@ ensures count==PRE(count)+1
  public final void addElement(Substitution x) {
    if( count == elements.length ) {
      Substitution[] newElements = new Substitution[ 2*(elements.length==0 ?
                                              2 : elements.length) ];
      System.arraycopy(elements, 0, newElements, 0, elements.length );
      /*@ assume (forall SubstitutionVec s; s==null || s.elements!=newElements) */
      elements = newElements;
    }
    elements[count++]=x;
  }

  //@ requires x!=null                                                // @@@@
  //@ modifies count
  public final boolean removeElement(Substitution x) {
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
  public final Substitution pop() {
    Substitution t = elements[--count];
    elements[count] = null;
    return t; 
  }


    //@ modifies count
    //@ ensures count==0
    public final void removeAllElements() {
        count = 0;
    }


  //@ requires 0 <= index && index <= this.count
  //@ requires obj!=null                                        // @@@@
  //@ modifies count
  //@ ensures count==PRE(count)+1
  public final void insertElementAt(Substitution obj, int index) {
    if( count == elements.length ) {
      Substitution[] newElements = new Substitution[ 2*(elements.length==0 ?
                                              2 : elements.length) ];
      System.arraycopy(elements, 0, newElements, 0, elements.length );
      /*@ assume (forall SubstitutionVec s; s==null || s==this
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
  public final void append(SubstitutionVec vec) {         //@ nowarn Exception
    for( int i=0; i<vec.size(); i++)
      addElement( vec.elementAt(i) );
  }
}
