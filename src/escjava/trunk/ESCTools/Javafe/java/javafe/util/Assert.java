/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.util;

/**
 * A class with static methods for checking assertions.
 * (Inspired by <cite>Mastering the AWT</code> by David Geary.)
 */

public class Assert
{
    //@ ensures false 
    static public void fail(String msg) {
	throw new AssertionFailureException(msg);
    }	  //@ nowarn Exception

    //@ requires b
    static public void notFalse(boolean b) {
	if (! b) throw new AssertionFailureException();
    }

    //@ requires b
    static public void notFalse(boolean b, String msg) {
	if (! b) throw new AssertionFailureException(msg);
    }

    //@ requires obj!=null
    static public void notNull(Object obj) {
	if (obj == null) throw new AssertionFailureException();
    }

    //@ requires obj!=null
    static public void notNull(Object obj, String msg) {
	if (obj == null) throw new AssertionFailureException(msg);
    }

    //@ ensures false
    static public void precondition() {
	throw new AssertionFailureException("Precondition violated!");
    }	  //@ nowarn Exception

    //@ ensures false
    static public void precondition(String msg) {
	throw new AssertionFailureException("Precondition violated: "+msg);
    }	//@ nowarn Exception

    //@ requires b
    static public void precondition(boolean b) {
	if (! b) throw new AssertionFailureException("Precondition violated!");
    }

    //@ ensures false
    static public void notImplemented() {
	throw new NotImplementedException("Hit an unimplemented feature");
    }	  //@ nowarn Exception

    //@ ensures false
    static public void notImplemented(String s) {
	throw new NotImplementedException("Not implemented: " + s);
    }	  //@ nowarn Exception
}
