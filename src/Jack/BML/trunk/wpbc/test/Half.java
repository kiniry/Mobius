/*
 * Created on Oct 28, 2004
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;

/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class Half {
	
      //@ requires n >= 0;
	  //@ ensures \result == \old(n)/2; 	 
	public int half(int n) {
		int a = 0;
		int constant = n;
		//@ loop_modifies n,a;
		//@ loop_invariant constant==n+2*a && n >= 0;
		//@ decreases n;
		while (n > 1) {
			a = a + 1;
			n = n - 2;
		}
		return a;
	}
}
