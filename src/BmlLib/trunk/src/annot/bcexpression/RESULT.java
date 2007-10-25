package annot.bcexpression;

import annot.bcclass.BCMethod;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.IDisplayStyle;
import annot.textio.Priorities;

/**
 * This class represents <code>\result</code> expression (return value of a
 * method). One <code>RESULT</code> per method.
 * 
 * @author tomekb
 */
public class RESULT extends BCExpression {

	/**
	 * Method whose return value it represents.
	 */
	private BCMethod m;

	/**
	 * Return type of method <code>m</code>.
	 */
	private JavaType1 type;

	/**
	 * A constructor for method initialization only. Later, use
	 * {@link BCMethod#getResult()} instead.
	 * 
	 * @param m -
	 *            initializing method.
	 */
	public RESULT(BCMethod m) {
		this.m = m;
		this.type = JavaType1.convert(m.getBcelMethod().getReturnType());
	}

	@Override
	protected JavaType1 checkType1() {
		return type;
	}

	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	@Override
	public JavaType1 getType() {
		return type;
	}

	@Override
	protected void init() {
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return IDisplayStyle._result;
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new ReadAttributeException("'read' method"
				+ " unavaliable, use BCMethod#getResult() instead.");
	}

	@Override
	public String toString() {
		return IDisplayStyle._result;
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.RESULT);
	}

}
