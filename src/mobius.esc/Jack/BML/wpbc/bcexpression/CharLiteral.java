/*
 * Created on Jul 12, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package bcexpression;

import bcexpression.javatype.JavaType;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class CharLiteral  extends Expression {

	private char literal;
	
		public CharLiteral(char _literal) {
			literal = _literal;
		}

		/* (non-Javadoc)
		 * @see bcexpression.Expression#getType()
		 */
		public Expression getType() {
			return JavaType.JavaCHAR;
		}
		/**
		 * @return Returns the literal.
		 */
		public char getLiteral() {
			return literal;
		}
	
		public boolean equals(Expression _expr) { 
			boolean equals = super.equals( _expr);
			if (equals == false ) {
				return false;
			}
			CharLiteral sl = (CharLiteral ) _expr;
			if ( getLiteral() != sl.getLiteral() ) {
				return false;
			}
			return true;
		}
	
		public Expression substitute(Expression _e1 , Expression _e2) { 
			return this;
		}
	
	
		public String toString() {
			return ""+literal;
		}

		/* (non-Javadoc)
		 * @see bcexpression.Expression#copy()
		 */
		public Expression copy() {
			return this;
		}
}
