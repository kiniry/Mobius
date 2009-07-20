/*
 * Created on 6 mai 2004
 *
 * To change the template for this generated file go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
package bytecode_wp.constants;

import bytecode_wp.bcexpression.Expression;
import bytecode_wp.bcexpression.StringLiteral;

/**
 * for thempmet not implemented - is there a need to treat these data strcutures?
 * @author io
 *
 * To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Generation - Code and Comments
 */
public class BCConstantUtf8 extends BCCONSTANT_LITERAL{
	private StringLiteral constant_string;
	/**
	 * @param _cp_index
	 */
	public BCConstantUtf8(int _cp_index, StringLiteral _s) {
		super(_cp_index);
		constant_string = _s;
	}

	/* (non-Javadoc)
	 * @see constants.BCCONSTANT_LITERAL#getLiteral()
	 */
	public Expression getLiteral() {
		// TODO Auto-generated method stub
		return constant_string;
	}
}
