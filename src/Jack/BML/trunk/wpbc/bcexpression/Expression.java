/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;


import bcexpression.javatype.*;
import type.BCType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public   abstract class  Expression {
	
	
	private Expression left;
	private Expression right;
	private BCType type;
	
	
	public static final NULL NULL = new NULL();
	
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
	
	/**
	 * @param 
	 */
	public abstract void setType( );


	
	
	/*public byte getExpressionType() {
		return type;
	}*/
	public   Expression getLeft() {
		return left; 
	}
	
	public  Expression getRight() {
		return right;
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) {
		if (_e1 instanceof ReferenceExpression) {
			
		}
		if (this.equals(_e1 ) ) {
			this.setLeft(_e2.getLeft()) ;
			this.setRight(_e2.getRight()) ;
			return this;	
		}
		setLeft( left.substitute(_e1, _e2 ));
		setRight(right.substitute(_e1, _e2 ));
		return this;
	}
		
	public abstract  BCType getType() ;

	public String toString() {
		return null;
	}
	
	
	public boolean equals(Expression _expr) {
		
		
		return false;
		
	}
}
