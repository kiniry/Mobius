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
public class JulienClass2 {
	int k = 3;
	
	//@ ensures k ==3; 
	public void m() {
		JulienClass1 jc = new JulienClass1();
		k = 3;
	}

}
