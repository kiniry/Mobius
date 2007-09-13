package annot.formula;

import annot.bcexpression.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

public class Predicate0Ar extends AbstractFormula {

	public static final Predicate0Ar TRUE = new Predicate0Ar(true);
	public static final Predicate0Ar FALSE = new Predicate0Ar(false);
	private boolean value;

	public Predicate0Ar(boolean value) {
		this.value = value;
	}

	@Override
	public String printCode1(BMLConfig conf) {
		return value ? "true" : "false";
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(value ? Code.TRUE : Code.FALSE);
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new ReadAttributeException("read() method unavaliable.");
	}

	@Override
	public int getPriority() {
		return 0;
	}

	@Override
	public void init() {
	}

	@Override
	public String toString() {
		return value ? "true" : "false";
	}

	@Override
	public JavaType getType1() {
		return JavaType.JavaBool;
	}

}
