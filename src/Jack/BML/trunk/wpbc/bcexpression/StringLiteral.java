/*
 * Created on 15 mars 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bcexpression;

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
		//setExpressionType(ExpressionConstants.STRING_LITERAL);
	}
}
