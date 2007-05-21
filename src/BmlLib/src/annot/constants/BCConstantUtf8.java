package annot.constants;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;
import annot.bcexpression.StringLiteral;

/**
 * for thempmet not implemented - is there a need to treat these data strcutures?
 * @author io
 */
public class BCConstantUtf8 extends BCCONSTANT_LITERAL{
	private StringLiteral constant_string;

	public BCConstantUtf8(int _cp_index, StringLiteral _s) {
		super(_cp_index);
		constant_string = _s;
	}

	public String printCode1(BMLConfig conf) {
		return constant_string.printCode(conf);
	}
	
	public String toString() {
		return "Utf8:	" + constant_string;
	}
	
	/* (non-Javadoc)
	 * @see constants.BCCONSTANT_LITERAL#getLiteral()
	 */
	public Expression getLiteral() {
		// TODO Auto-generated method stub
		return constant_string;
	}
}
