/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaType;
import type.BCType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ArithmeticExpression  extends Expression {
	private byte arithmetic_op ;
	
	public ArithmeticExpression(Expression _left, Expression _right, byte _arithmetic_op ) {
		super(_left,_right);
		arithmetic_op = _arithmetic_op;
	}
	
	
	
	public BCType getType() {
		return JavaType.JavaINT;
	}



	/* (non-Javadoc)
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
		
	}
	
}
