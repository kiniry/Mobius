/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import type.BCType;
import bcexpression.Expression;
import constants.BCConstantFieldRef;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ArrayElemFromTo extends JMLExpression {
	
	private Expression right;
	private int start;
	private int end;
	
	public ArrayElemFromTo( Expression _left, int _start, int _end) {
		super(_left);
		setStart(_start);
		setEnd(_end);
		
	}
	
	public int  getStart() {
		return start;
	}
	/**
	 * @return Returns the end.
	 */
	public int getEnd() {
		return end;
	}
	/**
	 * @param end The end to set.
	 */
	public void setEnd(int end) {
		this.end = end;
	}
	

	/**
	 * @param right The right to set.
	 */
	public void setRight(Expression right) {
		this.right = right;
	}
	/**
	 * @param start The start to set.
	 */
	public void setStart(int start) {
		this.start = start;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
		
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		// TODO Auto-generated method stub
		return null;
	}
}