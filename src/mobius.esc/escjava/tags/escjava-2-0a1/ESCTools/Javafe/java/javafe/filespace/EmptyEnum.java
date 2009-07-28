/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.filespace;


import java.util.*;


/**
 * EmptyEnum: This class simply implements an enumeration with
 *	       no elements.
 */

class EmptyEnum implements Enumeration {

    //@ invariant !moreElements
    //@ invariant !returnsNull

    EmptyEnum() {
	//@ set moreElements = false
	//@ set returnsNull = false
	//@ set elementType = \type(Object)
    }


    /** Returns true iff any more elements exist in this enumeration. */
    public boolean hasMoreElements() {
	return false;
    }

    /**
     * Returns the next element of the enumeration. Calls to this
     * method will enumerate successive elements.  Throws
     * NoSuchElementException if no more elements are left.
     */
    public Object nextElement()
	/*throws NoSuchElementException*/ {
	throw new NoSuchElementException();
    }
}
