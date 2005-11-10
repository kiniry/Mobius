/*
 * Created on Feb 11, 2005
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
public class M {
	int i = 0;
	
	//@ requires i == 2;
	//@ modifies i;
	//@ ensures i == \old(i) +  1;
	public void m() {
		i = i +1;
	}
	
	//@ requires i == 1;
	//@ modifies i;
	//@ ensures i > 0;
	public void n() {
		i = i +1;
		m();
		i = i +1;
	
	}
	
	
	

}
