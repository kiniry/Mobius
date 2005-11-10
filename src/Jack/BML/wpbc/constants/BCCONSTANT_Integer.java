/*
 * Created on Apr 28, 2004
 *
 * To change the template for this generated file go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
package constants;

import bcexpression.Expression;
import bcexpression.NumberLiteral;

/**
 * @author mpavlova
 *
 * To change the template for this generated type comment go to
 * Window>Preferences>Java>Code Generation>Code and Comments
 */
public class BCCONSTANT_Integer extends BCCONSTANT_LITERAL  {
	private NumberLiteral int_constant;
	
	public BCCONSTANT_Integer( int _cpIndex, int _constant) {
		super(_cpIndex);
		int_constant = new NumberLiteral(_constant);
	}
	

	/* (non-Javadoc)
	 * @see constants.BCCONSTANT_LITERAL#getLiteral()
	 */
	public Expression getLiteral() {
		return int_constant;
	}

}
