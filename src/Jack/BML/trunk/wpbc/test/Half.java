/*
 * Created on Aug 20, 2004
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
public class Half {
	/**
	 * @requires n >= 0
	 * 
	 * @ensures a = old (n ) div 2; 
	 */
	public int half(int n) {
		int a = 0;
		
		while (n != 0) {
			/*@ loop_invariant  old(n) = n + 2*a;
			  @ loop_modifies a, n;
			*/
			a = a + 1;
			n = n - 2;
		}
		return a;
	}


}
