package umbra.annot.bcexpression;

import umbra.annot.formula.Formula;


public class UnknownExpression extends Formula {

	public Expression copy() {
		return this;
	}

	public Expression substitute(Expression _e1, Expression _e2) {
		return this;
	}

	public String toString() {
		return "??";
	}

}
