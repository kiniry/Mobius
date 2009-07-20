/*
 * Created on Jul 29, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bytecode_wp.bcexpression;

import bytecode_wp.formula.Formula;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ConditionalExpression extends Expression {
	/*private Formula condition;*/
	
	public ConditionalExpression(Formula condition, Expression expr1, Expression expr2  ) {
		super(new Expression[]{condition, expr1, expr2});
		/*this.condition = condition;*/
	}
	
	
	public boolean equals(Expression expr) {
		boolean eq = super.equals(expr);
		return eq;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		
		if ( equals( _e1)) {
			return _e2;
		}
		
		Expression[] sExprs = getSubExpressions();
		sExprs[0] = sExprs[0].substitute(_e1, _e2);
		sExprs[1] = sExprs[1].substitute(_e1, _e2);
		sExprs[2] = sExprs[2].substitute(_e1, _e2);
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		Expression expr = getSubExpressions()[0];
		return expr.getType();
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = getSubExpressions()[0] + " ? " + getSubExpressions()[1] + " : " + getSubExpressions()[2];
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression expr0Copy = getSubExpressions()[0].copy();
		Expression expr1Copy = getSubExpressions()[1].copy();
		Expression expr2Copy = getSubExpressions()[2].copy();
		ConditionalExpression copy = new ConditionalExpression((Formula)expr0Copy, expr1Copy, expr2Copy);
		return copy;
	}

	/**
	 * @return
	 */
	public Formula getCondition() {
		return (Formula)getSubExpressions()[0];
	}

}
