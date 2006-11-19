package umbra.annot.bcexpression;


public class UnknownExpression extends Expression {

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
