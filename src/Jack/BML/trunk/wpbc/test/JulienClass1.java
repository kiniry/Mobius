/*
 * Created on Feb 4, 2005
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
public class JulienClass1 {
	public int i = 1;
	
	
	//@ public instance invariant i > 0;
	
	//@ ensures i  = 2;
	public  JulienClass1() {
		i = 2;
	}
	
	public void m() {
		
	}

}
