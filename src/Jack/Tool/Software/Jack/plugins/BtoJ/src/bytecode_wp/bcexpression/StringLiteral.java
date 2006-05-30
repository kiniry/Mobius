/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.bcexpression;

import bytecode_wp.bcexpression.javatype.JavaType;

/**
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class StringLiteral extends Expression {
	private String literal;
	
	public StringLiteral(String _literal) {
		literal = _literal;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#getType()
	 */
	public Expression getType() {
		return JavaType.JavaSTRING;
	}
	/**
	 * @return Returns the literal.
	 */
	public String getLiteral() {
		return literal;
	}
	
	public boolean equals(Expression _expr) { 
		boolean equals = super.equals( _expr);
		if (equals == false ) {
			return false;
		}
		StringLiteral sl = (StringLiteral ) _expr;
		if ( getLiteral() != sl.getLiteral() ) {
			return false;
		}
		return true;
	}
	
	public Expression substitute(Expression _e1 , Expression _e2) { 
		return this;
	}
	
	
	public String toString() {
		return literal;
	}

	/* (non-Javadoc)
	 * @see bcexpression.Expression#copy()
	 */
	public Expression copy() {
		return this;
	}
}
