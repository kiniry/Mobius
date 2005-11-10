/*
 * Created on Dec 6, 2004
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
public class Memory {
	 int memory;
	 int memoryBeforeLoop;
	 
	 

	//@ requires t +2 <= 10  ; 
	//@ modifies t;
	//@ ensures t <= \old(t) + 2 ;
	void m() {
		memory = memory + 2;
	}
	
	
	//@ requires t + 4 <= 10; 
	//@ modifies t;
	//@ ensures this.t <= \old(t) + 4;
	void n(){
		m();
		m();
	}	
}
