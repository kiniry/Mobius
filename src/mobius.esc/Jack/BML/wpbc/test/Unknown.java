/*
 * Created on Jan 20, 2005
 *
 * TODO To change the template for this generated file go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
package test;
import java.lang.NullPointerException;

/*class A {
	int v;
}
*/
/**
 * @author mpavlova
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class Unknown {
	int[] data;
	
	//@ ensures true;
	public void accessNull() {
		
		data[2] = 3;
	}
	
}
