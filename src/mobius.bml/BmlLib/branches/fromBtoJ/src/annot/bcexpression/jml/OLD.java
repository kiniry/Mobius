package annot.bcexpression.jml;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;
import annot.bcexpression.javatype.JavaType;

public class OLD extends JMLExpression {

//	private JavaType type;

	public OLD(Expression _left) {
		super(_left);
		priority = -1; // always needs parenthness around its argument
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
//	public Expression getType() {
//		Expression type = getSubExpressions()[0].getType();
//		return type;
//	}
//
//	public Expression rename(Expression expr1, Expression expr2) {
//		return this;
//	}
//
//	/* (non-Javadoc)
//	 * @see bcexpression.Expression#substitute(bcexpression.Expression, bcexpression.Expression)
//	 */
//	/**
//	 * the substitution is realised iff the expression to be substituted - _e1 is equal to this expression 
//	 * otherwise the result of the substitution is the same expression. 
//	 */
//	public Expression substitute(Expression _e1, Expression _e2) {
//		if (equals(_e1)) {
//			return _e2;
//		}
//		return this;
//	}

	public String printCode1(BMLConfig conf) {
		Expression expr = getSubExpressions()[0];
		String s = "old" + expr.printCode(conf);
		return s;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		Expression[] copySubExpressions = copySubExpressions();
		OLD copy = new OLD(copySubExpressions[0]);
		return copy;
	}

//	public Expression atState(int state) {
//		return this;
//	}
//
//	public Expression atState(int state, Expression expr) {
//		return this;
//	}
//
//	public boolean isBooleanType() {
//		if (type == JavaType.JavaBOOLEAN) {
//			return true;
//		}
//		return false;
//	}
}
