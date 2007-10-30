package annot.bcexpression.modifies;

import annot.io.Code;
import annot.textio.BMLConfig;

public class ModifiesStar extends SpecArray {

	public ModifiesStar() {
		super(Code.MODIFIES_STAR);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return "*";
	}

	@Override
	public String toString() {
		return "[*]";
	}

}
