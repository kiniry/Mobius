/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package vm;

import java.util.Vector;



/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class Stack {
	private Vector stack;
	private StackTop top;
	

	
	public void push( Object _value ) {
		if (stack == null) {
			stack = new Vector();
			top = new StackTop();
		}
		stack.add( _value);
		top.inc(1);
	}
	
	public Object pop() {
		if (stack == null) {
			return null;
		}
		Object obj;
		obj = stack.remove(top.getTop());
		top.dec(1);
		return obj;	
	}
		
}
