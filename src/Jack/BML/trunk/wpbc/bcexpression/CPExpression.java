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
public class CPExpression extends Expression {
	private BCConstant left;
	private Expression right;
	
	public CPExpression(){}
	
	public CPExpression(BCConstant _right, Expression _left) {
		setLeft(_right);
		setRight(_left);
		//setExpressionType(_type);
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
	
	
	public Object getLeft() {
		return left;
	}
	
	public Object getRight(){
		return right;
	}
}
