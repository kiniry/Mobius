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
public class AllArrayElem  extends JMLExpression {
	private BCConstantFieldRef left;
	private Expression right;
	
	public AllArrayElem( BCConstantFieldRef _left, Expression _right) {
		setLeft(_left);
		setRight(right);
		
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
}
