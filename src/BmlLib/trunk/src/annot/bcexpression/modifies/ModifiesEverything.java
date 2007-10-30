package annot.bcexpression.modifies;

import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents any side effect of described code,
 * or that side effects are unknown.
 * This is a singleton, it has only one instance
 * ({@link ModifyExpression#Everything}).
 */
public class ModifiesEverything extends ModifyExpression {

	/**
	 * A constructor for superclass only. Use
	 * {@link ModifyExpression#Everything} instead.
	 */
	protected ModifiesEverything() {
		super(Code.MODIFIES_EVERYTHING);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return "everything";
	}

	@Override
	public String toString() {
		return "everything";
	}

}
