/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.vm;


import type.BCType;
import bcexpression.Expression;
import bcexpression.Variable;



/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public final class Stack extends Expression  {
	
	
	public Expression counter;
	
	public Stack(Expression _counter) {
		counter = _counter;
	}
	
	/*
	 * this expression has the Top type, i.e. it may receive as value any other expression of any type 
	 *  (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
		
	}


	public String toString() {
		return "StackTop(" + counter.toString() + ")"; 
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	} 
		
}
