/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression.jml;

import bcexpression.Expression;
import constants.BCConstantFieldRef;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class ArrayElemFromTo extends JMLExpression {
	private BCConstantFieldRef left;
	private Expression right;
	private int start;
	private int end;
	
	public ArrayElemFromTo(BCConstantFieldRef _left, Expression _right, int _start, int _end) {
		setLeft(_left);
		setRight(_right);
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
	 * @return Returns the left.
	 */
	public Object getLeft() {
		return left;
	}
	/**
	 * @param left The left to set.
	 */
	public void setLeft(BCConstantFieldRef left) {
		this.left = left;
	}
	/**
	 * @return Returns the right.
	 */
	public Object getRight() {
		return right;
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
}