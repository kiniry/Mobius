/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package vm;



/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class StackTop {
	private int top = -1;
	
	public void inc( int _j) {
		top = top + _j;
	}
	
	public void dec(int _j) {
		top = top - _j;
	} 
	
	public int getTop() {
		return top;
	}
}
