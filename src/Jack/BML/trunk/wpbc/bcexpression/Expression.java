/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;


import bcexpression.type.*;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public   class  Expression {
	
	
	private Expression left;
	private Expression right;
	
	private JavaType type;
	
	protected Expression() {
	}
	
	public Expression( Expression _left, Expression _right)  {;
		setLeft(_left);
		setRight(_right);		
	}
	
	/**
	 * @param right2
	 */
	public void setRight(Expression right2) {
		right = right2;
		
	}
	
	/**
	 * @param left2
	 */
	public void setLeft(Expression left2) {
		left = left2;
	}
	
	
	
	
	/*public byte getExpressionType() {
		return type;
	}*/
	public   Object getLeft() {
		return left; 
	}
	
	public  Object getRight() {
		return right;
	}
	
	public void substitute(Expression expr , Object value) {
	}
	
	
	public JavaType getType() {
		return type;
	}
	
}
