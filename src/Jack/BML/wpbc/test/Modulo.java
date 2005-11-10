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
public class Modulo {
	
	/*
	 * this = loc(0) i = loc(1) k = loc(2) constant = loc(3) s = loc( 4 )
	 */
		//@ requires true;
		//@ ensures \result == \old(i) % k;
		public static int mod(int i, int k) {
			int constant = i;
			
			//@  loop_modifies i, s;
			//@  loop_invariant constant == s * k + i ;
			//@  decreases i;
			for (int s = 0;
			true; 
			s++) {
				if (i <= k) {
					break;
				}
				i = i - k; // loc(1) = loc(1) - loc( 2 )
			}
			if (i == k) {
				return 0;
			}
			return i;
		}
		
		public static void main(String[] args) {
			mod(7,3);
		} 
		
	/*	
		 * this = loc(0) i = loc(1) k = loc(2) constant = loc(3) s = loc( 4 )
		 
			//@ requires true;
			//@ ensures \result == \old(i) % k;
			public int mod1(int k) {
				int constant = i;
				
				//@  loop_modifies i, s;
				//@  loop_invariant constant == s * k + i ;
				//@  decreases i;
				for (int s = 0; true; s++) {
					if (i <= k) {
						break;
					}
					i = i - k; // loc(1) = loc(1) - loc( 2 )
				}
				if (i == k) {
					return 0;
				}
				return i;
			}*/

}
