/*
 * Created on Apr 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcexpression;


/**
 * @author mpavlova
 * 
 * the class represents bit expressions
 */
public class BitExpression extends Expression {
	private byte bitwise_op;

	//bitwise expressions
	public static final byte  SHL  = 31;
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
	public Expression getType() {
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
	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String op = null;
		switch ( bitwise_op ) {
		
		case ExpressionConstants.BITWISEAND  : { op = "&" ; break;}
		case ExpressionConstants.BITWISEOR :    { op = "|" ; break;}
		case ExpressionConstants.BITWISEXOR :    { op = "xor" ; break;}
		}
		Expression[] subExp = getSubExpressions();
		String s = subExp[0] + op + subExp[1];
		return s;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] copySubExpr = copySubExpressions();
		BitExpression copy = new BitExpression(copySubExpr[0], copySubExpr[1], bitwise_op );
		return copy;
	}
}
