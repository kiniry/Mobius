/*
 * Created on Sep 30, 2004
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
public class G {
	public int x;
	public int y;
	
	//@ requires y == 3;
	//@ modifies x;
	//@ ensures x == 2;
	public void test() {
		if (y == 3) {
			x = 1; 
		} else {
			x = 2;
		}
	}
 
}
