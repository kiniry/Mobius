/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package test;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class WPTest {
	int i;
	
	/*
	 * @ requires i == 1;
	 * @ ensures \result == i;
	 *
	 **/
	public int m() {
		return i;
	} 
	
	/*
	 * @ ensures \result > 0
	 */
	public int n(){
		return m();
	}
	
	public int l() {
		return i + 1;
	}
	public int k() {
		i =  i +1;
		if( i == 1) {
				return m();
		} else {
				return n();
		}
	}
}
