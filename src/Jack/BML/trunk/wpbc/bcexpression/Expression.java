/*
 * Created on 8 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;
import bcexpression.vm.Counter;
import type.BCType;
/**
 * @author io
 * 
 * To change the template for this generated type comment go to Window -
 * Preferences - Java - Code Generation - Code and Comments
 */
public abstract class Expression implements Cloneable {
	private Expression[] subExpressions;
	public static final Counter COUNTER = Counter.getCounter();
	public static final ArithmeticExpression COUNTER_PLUS_2 = ArithmeticExpression.getArithmeticExpression(
			COUNTER, new NumberLiteral(2), ExpressionConstants.ADD);
	public static final ArithmeticExpression COUNTER_PLUS_1 = ArithmeticExpression.getArithmeticExpression(
			COUNTER, new NumberLiteral(1), ExpressionConstants.ADD);
	public static final ArithmeticExpression COUNTER_MINUS_1 = ArithmeticExpression.getArithmeticExpression(
			COUNTER, new NumberLiteral(1), ExpressionConstants.SUB);
	public static final ArithmeticExpression COUNTER_MINUS_2 = ArithmeticExpression.getArithmeticExpression(
			COUNTER, new NumberLiteral(2), ExpressionConstants.SUB);
	public static final ArithmeticExpression COUNTER_MINUS_3 = ArithmeticExpression.getArithmeticExpression(
			COUNTER, new NumberLiteral(3), ExpressionConstants.SUB);
	public static final ArithmeticExpression COUNTER_MINUS_4 = ArithmeticExpression.getArithmeticExpression(
			COUNTER, new NumberLiteral(4), ExpressionConstants.SUB);
	public static final NULL NULL = new NULL();
	protected Expression() {
	}
	public Expression(Expression _subExpr) {
		subExpressions = new Expression[1];
		subExpressions[0] = _subExpr;
	}
	public Expression(Expression _subExpr1, Expression _subExpr2) {
		subExpressions = new Expression[2];
		subExpressions[0] = _subExpr1;
		subExpressions[1] = _subExpr2;
	}
	public Expression(Expression[] _subExprs) {
		if (_subExprs != null) {
			subExpressions = _subExprs;
		}
	}
	
	/**
	 * @return Returns the subExpressions.
	 */
	public Expression[] getSubExpressions() {
		return subExpressions;
	}
	/**
	 * @param subExpressions
	 *            The subExpressions to set.
	 */
	protected void setSubExpressions(Expression[] subExpressions) {
		this.subExpressions = subExpressions;
	}
	/**
	 * substitute the subexpression (if there are ) equal to _e1 with _e2
	 * 
	 * @param _e1
	 * @param _e2
	 * @return - this object with the substitutions made
	 */
	public abstract Expression substitute(Expression _e1, Expression _e2);
	public abstract BCType getType();
	
	public String toString() {
		return null;
	}
	/**
	 * two expressions are equals if they are from the same type and if they
	 * have the same number of subexpressions and they are equals.
	 * 
	 * @param _expr
	 * @return
	 */
	public boolean equals(Expression _expr) {
		if (_expr == null) {
		}
		if (_expr.getClass() != this.getClass()) {
			return false;
		}
		//		test if the subexpressions are equal
		Expression[] subEofThis = getSubExpressions();
		Expression[] subEofExpr = _expr.getSubExpressions();
		if (((subEofExpr == null) && (subEofThis != null))
				|| ((subEofExpr != null) && (subEofThis == null))) {
			return false;
		}
		//both expressions don't have subexpressions
		if ((subEofExpr == null) && (subEofThis == null)) {
			return true;
		}
		boolean subExprEquals = true;
		if ((subEofExpr != null) && (subEofThis != null)) {
			for (int i = 0; i < subEofThis.length; i++) {
				subExprEquals = subExprEquals
						&& subEofThis[i].equals(subEofExpr[i]);
			}
		}
		return subExprEquals;
	}
	public Expression copy() {
		Expression copy = null;
		return copy;
	}
	
}
