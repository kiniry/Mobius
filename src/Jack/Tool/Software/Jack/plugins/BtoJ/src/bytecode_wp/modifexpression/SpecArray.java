/*
 * Created on Sep 15, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.modifexpression;

import bytecode_wp.bcexpression.Expression;

/**
 * @author mpavlova
 * 
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public abstract class SpecArray extends Expression {
	public SpecArray() {
	}

	public SpecArray(Expression expr) {
		super(expr);
	}

	public SpecArray(Expression expr1, Expression expr2) {
		super(expr1, expr2);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#substitute(bcexpression.Expression,
	 *      bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		if (this.equals(_e1)) {
			return _e2;
		}
		Expression[] exprs = getSubExpressions();
		if (exprs != null) {

			for (int i = 0; i < exprs.length; i++) {
				exprs[i] = exprs[i].substitute(_e1, _e2);
			}
			setSubExpressions(exprs);
		}
		return this;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		if (this instanceof AllArrayElem) {
			return AllArrayElem.ALLARRAYELEM;
		}
		Expression[] exprs = getSubExpressions();
		Expression[] exprsCopy = new Expression[exprs.length];
		for (int i = 0; i < exprs.length; i++) {
			exprsCopy[i] = exprs[i].copy();
		}

		if (this instanceof SingleIndex) {
			SingleIndex copy = new SingleIndex(exprsCopy[0]);
			return copy;
		}
		if (this instanceof ArrayElemFromTo) {
			ArrayElemFromTo copy = new ArrayElemFromTo(exprsCopy[0],
					exprsCopy[1]);
			return copy;
		}
		return null;
	}

}
