/*
 * Created on Jan 24, 2005
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
public class TestIfTrue {
	
	//@ ensures \result == 1;
	public int ifTrue(boolean cond) {
		if (cond) {
			int i =0 ;
			i = i + 1;
			return 1;
		}
		return 0;
	}
	
	

}
