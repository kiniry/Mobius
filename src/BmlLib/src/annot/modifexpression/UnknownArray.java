package annot.modifexpression;

import annot.bcexpression.Expression;

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

	public String toString() {
		System.out.println("Unknown array");
		return "?";
	}
	
	public Expression copy() {
		return this;
	}
}
