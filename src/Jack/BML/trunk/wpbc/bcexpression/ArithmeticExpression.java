/*
 * Created on Mar 4, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

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
	
}
