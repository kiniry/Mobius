/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.modifexpression;

 
import bytecode_wp.bcexpression.Expression;


/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ArrayElemFromTo extends SpecArray {

	
	public ArrayElemFromTo( Expression _start, Expression _end) {
		super(_start, _end);
	}

	public Expression getStart() {
		Expression start = getSubExpressions()[0];
		return start;
	}
	
	public Expression getEnd() {
		Expression end = getSubExpressions()[1];
		return end;
	}
		
	

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 
	public Expression substitute(Expression _e1, Expression _e2) {
		return this;
	}*/

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		Expression[] exprs =  getSubExpressions();
		return exprs[0] + " .. "+ exprs[1];
	}

/*	 (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 
	public Expression copy() {
		Expression[] exprs =  getSubExpressions();
		Expression copyStart = exprs[0].copy(); 
		Expression copyEnd = exprs[1].copy();
		ArrayElemFromTo copyThis= new ArrayElemFromTo(copyStart, copyEnd);
		return copyThis;
	}*/
}