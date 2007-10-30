package annot.bcexpression.modifies;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
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
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new RuntimeException("'read' method unavaliable");
	}

	@Override
	public String toString() {
		return "[*]";
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.MODIFIES_STAR);
	}

	@Override
	protected void init() {}

}
