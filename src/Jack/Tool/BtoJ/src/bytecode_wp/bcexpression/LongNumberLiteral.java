package bytecode_wp.bcexpression;

import bytecode_wp.bcexpression.javatype.JavaBasicType;

public class LongNumberLiteral extends ArithmeticExpression {
private long literal;

	

	
	/**
	 * this constructor expects that _literal must be a correct representation
	 * of an integer litreral.
	 * 
	 * @param _literal -
	 *            a string representation of integer e.g. new
	 *            NumberLiteral("12")
	 */
	public LongNumberLiteral(long  _literal) {
		literal = _literal;
	}

	/**
	 * @param value -
	 *            a correct value
	 * @param radix -
	 *            the radix in which the value is interpreted
	 */
	/*
	 * public NumberLiteral(int _literal, JavaBasicType _type) { literal =
	 * _literal; type = _type; }
	 */

	/*
	 * (non-Javadoc)
	 * 
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return JavaBasicType.JavaINT;
	}

	/**
	 * @return Returns the value.
	 */
	public long getLiteral() {
		return literal;
	}

	public String toString() {
		try {
			return "" + literal;
		} catch (NullPointerException e) {
			e.printStackTrace();
			return "numberLiteral +  null";
		}
	}

	public boolean equals(Expression _expr) {
		try {
			boolean equals = super.equals(_expr);

			if (equals == false) {
				return false;
			}
			NumberLiteral nl = (NumberLiteral) _expr;
			if (getType() != nl.getType()) {
				return false;
			}
			if (getLiteral() != nl.getLiteral()) {
				return false;
			}
			return true;
		} catch (NullPointerException e) {
			e.printStackTrace();
			return false;
		}
	}

	public Expression substitute(Expression _e1, Expression _e2) {
		return this;
	}

	public Expression copy() {
		return this;
	}
}
