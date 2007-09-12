package annot.constants;

import annot.bcexpression.StringLiteral;

//import bytecode_wp.bcexpression.Expression;
//import bytecode_wp.bcexpression.StringLiteral;

public class BCCONSTANT_String extends BCConstant {
	StringLiteral string_literal;
	
	public BCCONSTANT_String(int _cp_index, String _literal ) {
		super(_cp_index);
		string_literal = new StringLiteral(_literal);
	}

	public String toString() {
		return "String:	" + string_literal;
	}

//	/**
//	 * @return the literal that this data structure contains
//	 */
//	public Expression getLiteral() {
//		return string_literal;
//	}
}
