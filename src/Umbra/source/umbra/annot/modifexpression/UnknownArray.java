package umbra.annot.modifexpression;

import umbra.annot.bcexpression.Expression;

// atrapa SpecArray
public class UnknownArray extends SpecArray {
	public UnknownArray() {
	}

	public UnknownArray(Expression expr) {
		super(expr);
	}

	public UnknownArray(Expression expr1, Expression expr2) {
		super(expr1, expr2);
	}

	public Expression copy() {
		return this;
	}
	
	public String toString() {
		return "?[]";
	}
}
