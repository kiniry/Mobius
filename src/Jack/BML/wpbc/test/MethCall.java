/*
 * Created on Mar 29, 2005
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
public class MethCall {
	int i = 0;
	
	//@ requires i == 0;
	//@ modifies i;
	//@ ensures i == 3; 
	public void m(){
		i = i+3;
	}
	
	//@ requires i == 0;
	//@ modifies i;
	//@ ensures i >= 6;
	public void n(){
		i = 3;
		m();
	}
	
}
