package annot.bcexpression.modifies;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
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

	/**
	 * This class is a singleton, it has no constructor from
	 * AttributeReader.
	 */
	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new RuntimeException("There is nothing" +
		" to read by ModifiesEverything expression.");
	}

	@Override
	public String toString() {
		return "everything";
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.MODIFIES_EVERYTHING);
	}

	@Override
	protected void init() {}

}
