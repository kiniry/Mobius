/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;
import type.BCType;
/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BitExpression extends Expression {
	private byte bitwise_op;
	public BitExpression(Expression _left, Expression _right, byte _op) {
		super(_left, _right);
		bitwise_op = _op;
	}
	public byte getBitwiseOperation() {
		return bitwise_op;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#setType()
	 */
	public void setType() {
		// TODO Auto-generated method stub
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		// TODO Auto-generated method stub
		return null;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#equals(bcexpression.Expression)
	 */
	public boolean equals(Expression _expr) {
		boolean equals = super.equals(_expr);
		if (equals == true) {
			BitExpression bitExpr = (BitExpression) _expr;
			equals = equals
					&& (bitExpr.getBitwiseOperation() == getBitwiseOperation()
							? true
							: false);
		}
		return equals;
	}
	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#substitute(bcexpression.Expression,
	 *      bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (equals(_e1)) {
			return _e2;
		}
		Expression[] subExpr = getSubExpressions();
		for (int i = 0; i < subExpr.length; i++) {
			subExpr[i] = subExpr[i].substitute(_e1, _e2);
		}
		return this;
	}
}
