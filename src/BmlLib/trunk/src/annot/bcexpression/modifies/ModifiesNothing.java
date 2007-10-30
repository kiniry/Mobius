package annot.bcexpression.modifies;

import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents no side effect of described code.
 * This is a singleton, it has only one instance
 * ({@link ModifyExpression#Nothing}).
 */
public class ModifiesNothing extends ModifyExpression {

	/**
	 * A constructor for superclass only. Use
	 * {@link ModifyExpression#Nothing} instead.
	 */
	protected ModifiesNothing() {
		super(Code.MODIFIES_NOTHING);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return "nothing";
	}

	@Override
	public String toString() {
		return "nothing";
	}

}
