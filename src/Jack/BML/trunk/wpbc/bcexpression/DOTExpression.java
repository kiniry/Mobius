/*
 * Created on 14 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

import constants.BCConstant;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public abstract class DOTExpression extends Expression implements ReferenceExpression {
	private BCConstant left;
	private Expression right;
	
	public DOTExpression(){}
	
	public DOTExpression(BCConstant _left, Expression _right) {
		setLeft(_left);
		setRight(_right);
		setType();
	}
	
	public DOTExpression(Expression _right, Expression _left) {
		setLeft(_left);
		setRight(_right);
		setType();
	}
	
	/**
	 * @param right2
	 */
	private void setLeft(BCConstant _constant) {
		left = _constant;
	}
	
	/**
	 * @param left2
	 */
	public void setRight(Expression right2) {
		right = right2;
	}
	
	

	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
		
	}
}
