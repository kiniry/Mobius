/*
 * Created on Jul 29, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import formula.Formula;
import type.BCType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class ConditionalExpression extends Expression {
	private Formula condition;
	
	public ConditionalExpression(Formula condition, Expression expr1, Expression expr2  ) {
		super(expr1, expr2);
		this.condition = condition;
	}
	
	
	public boolean equals(Expression expr) {
		boolean eq = super.equals(expr);
		if (!eq ) {
			return false;
		}
		ConditionalExpression conditionalExpr = (ConditionalExpression) expr;
		Formula _condition = conditionalExpr.getCondition();
		eq = condition.equals(_condition);
		return eq;
	}
	/* (non-Javadoc)
	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
	 */
	public Expression substitute(Expression _e1, Expression _e2) {
		
		if ( equals( _e1)) {
			return _e2;
		}
		condition =  (Formula)condition.substitute(_e1, _e2);
		Expression[] sExprs = getSubExpressions();
		sExprs[0] = sExprs[0].substitute(_e1, _e2);
		sExprs[1] = sExprs[1].substitute(_e1, _e2);
		return this;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public BCType getType() {
		Expression expr = getSubExpressions()[0];
		return expr.getType();
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#toString()
	 */
	public String toString() {
		String s = condition + " ? " + getSubExpressions()[0] + " : " + getSubExpressions()[1];
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Formula conditionCopy = (Formula)condition.copy();
		Expression expr0Copy = getSubExpressions()[0].copy();
		Expression expr1Copy = getSubExpressions()[1].copy();
		ConditionalExpression copy = new ConditionalExpression(conditionCopy, expr0Copy, expr1Copy);
		return copy;
	}

	/**
	 * @return
	 */
	public Formula getCondition() {
		return condition;
	}

}
