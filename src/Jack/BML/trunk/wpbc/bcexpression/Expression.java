/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;


import bcexpression.javatype.*;
import bcexpression.vm.Counter;
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
	
	private static final Counter counter  = Counter.getCounter();
	
	private static final ArithmeticExpression counter_plus_1  = new ArithmeticExpression(
															counter,
															new NumberLiteral("1", 10, JavaType.JavaINT),
															ExpressionConstants.ADD);
	
	private static final ArithmeticExpression counter_minus_1  = new ArithmeticExpression(
															counter,
															new NumberLiteral("1", 10, JavaType.JavaINT),
															ExpressionConstants.SUB);
	
	private static final ArithmeticExpression counter_minus_2  = new ArithmeticExpression(
																counter,
																new NumberLiteral("2", 10, JavaType.JavaINT),
																ExpressionConstants.SUB);
																
	private static final ArithmeticExpression counter_minus_3  = new ArithmeticExpression(
																counter,
																new NumberLiteral("3", 10, JavaType.JavaINT),
																ExpressionConstants.SUB);						
																									
	public static final NULL NULL = new NULL();
	
	protected Expression() {
	}
	
	public Expression( Expression _left, Expression _right)  {;
		setLeft(_left);
		setRight(_right);		
	}
	
	public static Counter getCounter() {
		return counter;
	}
	
	public static ArithmeticExpression getCounter_plus_1() {
		return counter_plus_1 ;
	}
	
	public static ArithmeticExpression getCounter_minus_1() {
		return counter_minus_1 ;
	}
	
	public static ArithmeticExpression getCounter_minus_2() {
		return counter_minus_2;
	}
	
	public static ArithmeticExpression getCounter_minus_3() {
		return counter_minus_3;
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
	
//	/**
//	 * @param 
//	 */
//	public abstract void setType( );
//

	
	
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
//		if (_e1 instanceof FieldAccessExpression) {
//			return this;	
//		}
		
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
