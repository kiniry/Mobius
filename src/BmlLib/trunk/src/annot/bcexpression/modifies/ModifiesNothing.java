package annot.bcexpression.modifies;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents no side effect of described code. This is a singleton,
 * it has only one instance ({@link ModifyExpression#Nothing}).
 */
public class ModifiesNothing extends ModifyExpression {

	/**
	 * A constructor for superclass only. Use {@link ModifyExpression#Nothing}
	 * instead.
	 */
	protected ModifiesNothing() {
		super(Code.MODIFIES_NOTHING);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return "nothing";
	}

	/**
	 * This class is a singleton, it has no constructor from AttributeReader.
	 */
	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new RuntimeException("There is nothing"
				+ " to read by ModifiesNothing expression.");
	}

	@Override
	public String toString() {
		return "nothing";
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.MODIFIES_NOTHING);
	}

	@Override
	protected void init() {
	}

}
