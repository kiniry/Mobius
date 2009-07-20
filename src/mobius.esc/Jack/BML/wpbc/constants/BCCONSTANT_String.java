/*
 * Created on Apr 28, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package constants;

import bcexpression.Expression;
import bcexpression.StringLiteral;

/**
 * @author mpavlova
 *
 */
public class BCCONSTANT_String extends BCConstant {
	StringLiteral string_literal;
	
	public BCCONSTANT_String(int _cp_index, String _literal ) {
		super(_cp_index);
		string_literal = new StringLiteral(_literal);
	}
	
	/**
	 * @return the literal that this data structure contains
	 */
	public Expression getLiteral() {
		return string_literal;
	}

}
