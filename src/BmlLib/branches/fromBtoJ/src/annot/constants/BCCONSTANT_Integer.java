package annot.constants;

import annot.bcclass.BMLConfig;
import annot.bcexpression.Expression;
import annot.bcexpression.NumberLiteral;
//import bytecode_wp.bcexpression.NumberLiteral;

public class BCCONSTANT_Integer extends BCCONSTANT_LITERAL  {
	private NumberLiteral int_constant;
	
	public BCCONSTANT_Integer( int _cpIndex, int _constant) {
		super(_cpIndex);
		int_constant = new NumberLiteral(_constant);
	}

	public String printCode1(BMLConfig conf) {
		return ""+int_constant;
	}
	
	public String toString() {
		return "INT:	" + int_constant;
	}
	
//	/* (non-Javadoc)
//	 * @see constants.BCCONSTANT_LITERAL#getLiteral()
//	 */
//	public Expression getLiteral() {
//		return int_constant;
//	}
}
