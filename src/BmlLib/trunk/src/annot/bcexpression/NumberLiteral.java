package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

public class NumberLiteral extends AbstractIntExpression {

	private int value;

	public NumberLiteral(int literal) {
		super(Code.INT_LITERAL);
		this.value = literal;
	}

	public NumberLiteral(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	public int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public String printCode1(BMLConfig conf) {
		return "" + value;
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		value = ar.readInt();
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.INT_LITERAL);
		aw.writeInt(value);
	}

	@Override
	public void init() {
	}

	@Override
	public String toString() {
		return "" + value;
	}

}
