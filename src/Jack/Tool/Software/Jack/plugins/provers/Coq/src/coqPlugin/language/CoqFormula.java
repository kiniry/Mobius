package coqPlugin.language;

import jml2b.formula.IFormToken;

public class CoqFormula implements IFormToken{

	protected final byte nodetype;
	
	protected CoqFormula(byte b) {
		nodetype = b;
	}
}
