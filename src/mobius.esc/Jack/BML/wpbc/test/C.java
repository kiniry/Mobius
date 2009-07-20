/*
 * Created on Sep 20, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package test;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class C {

	 //@ requires true;
	 //@ modifies \nothing; 
	 //@ ensures \result != null;
	public B m1() {
		B b = new B(5, 5);
		return b;
	}
}
