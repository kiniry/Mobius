/*
 * Created on Feb 18, 2005
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
public class Square {

	//@ requires n >= 0;
	//@ ensures  \result == n*n;
	public static int  sqr(int n) {
		if (n == 0) {
			return 0;
		} else {
			int s = (2*n -1 )  + sqr( n -1);
			return s;
		}
		
	}
	
	
	
	
	
}
