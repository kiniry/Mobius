package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents <code>null</code> value.
 * Singleton.
 * 
 * @author tomekb
 */
public class NULL extends BCExpression {

	/**
	 * A standard constructor.
	 */
	public NULL() {
		super(Code.NULL);
	}
	
	@Override
	protected JavaType1 checkType1() {
		return JavaReferenceType.ANY;
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType1 getType() {
		return JavaReferenceType.ANY;
	}

	@Override
	protected void init() {}

	@Override
	protected String printCode1(BMLConfig conf) {
		return "null";
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new ReadAttributeException("There is nothing" +
			" to read for null expression.");
	}

	@Override
	public String toString() {
		return "null";
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.NULL);
	}

}
