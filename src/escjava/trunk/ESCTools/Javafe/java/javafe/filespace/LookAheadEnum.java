/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.filespace;


import java.util.Enumeration;
import java.util.NoSuchElementException;


/**
 * This layer describes how to implement an {@link Enumeration} in
 * terms of a single function that returns the next element in a
 * series, or null if the series is exhausted.<p>
 *
 * Using one function instead of the two used by {@link Enumeration}
 * has the advantage of avoiding possible duplication of code to
 * determine whether or not any elements remain in the series.<p>
 *
 * Limitation: <code>null</code> cannot belong to the resulting
 * {@link Enumeration}s.<p>
 */

abstract class LookAheadEnum implements Enumeration {

    //@ invariant !returnsNull


    /*
     * Object invariant: If lookAheadValid is true, then
     * calcNextElement has already been called and its result slashed in
     * lookAhead.<p>
     *
     * In particular, if lookAheadValid is true and lookAhead == null,
     * then we are exhausted.  If lookAheadValid is true and lookAhead
     * is non-null, then lookAhead contains the next element of the
     * series.<p>
     */

    //@ invariant lookAheadValid ==> moreElements == (lookAhead != null)

    private boolean lookAheadValid = false;

    //@ invariant \typeof(lookAhead) <: elementType || lookAhead==null;
    private Object lookAhead = null;


    /**
     * Ensure that lookAheadValid is set, calling calcNextElement if
     * needed.
     */
    //@ modifies lookAheadValid, lookAhead	// NOT moreElements
    //@ ensures lookAheadValid
    private void ensureLookedAhead() {
	if (!lookAheadValid) {
	    lookAhead = calcNextElement();
	    /*
	     * We assume that moreElements magically predicted
	     * calcNextElement()'s output:
	     */
	    //@ assume moreElements == (lookAhead != null)
	    lookAheadValid = true;
        }
    }
	

    /***************************************************
     *                                                 *
     * Creation:				       *
     *                                                 *
     **************************************************/

    /**
     * Create an look-ahead enumerator that will return the non-null
     * results of calcNextElement().
     */
    //@ ensures !lookAheadValid
    //@ ensures lookAhead==null		// So subclass can set elementType...
    public LookAheadEnum() {
	//@ set elementType = \type(Object)	// override in subclasses...
	//@ set returnsNull = false
    }

    /**
     * Create a look-ahead enumerator that will return first followed
     * by the non-null results of calcNextElement().
     */
    //@ requires first != null;
    //@ ensures moreElements
    //   So subclass can set elementType...:
    //@ ensures \typeof(lookAhead) <: \typeof(first)
    public LookAheadEnum(Object first) {
	//@ set elementType = \type(Object)	// override in subclasses...
	//@ set returnsNull = false

	lookAheadValid = true;
	lookAhead = first;

	//@ set moreElements = true
    }


    /***************************************************
     *                                                 *
     * Handling the Enumeration interface:	       *
     *                                                 *
     **************************************************/

    /** Returns true iff any more elements exist in this enumeration. */
    public final boolean hasMoreElements() {
	ensureLookedAhead();

	return lookAhead != null;
    }

    /**
     * Returns the next element of the enumeration. Calls to this
     * method will enumerate successive elements.  Throws
     * NoSuchElementException if no more elements are left.
     */
    public final Object nextElement()
		/* throws NoSuchElementException*/ {
	ensureLookedAhead();

	if (lookAhead == null)
	    throw new NoSuchElementException();

	lookAheadValid = false;
	return lookAhead;
    }


    /***************************************************
     *                                                 *
     * Calculating the next element:		       *
     *                                                 *
     **************************************************/

    /**
     * Compute the next element in the series, or return null if the
     * series is exhausted.
     *
     * This function will never be called again once it returns null.
     */
    //@ ensures \typeof(\result) <: elementType || \result==null;
    protected abstract Object calcNextElement();

}
