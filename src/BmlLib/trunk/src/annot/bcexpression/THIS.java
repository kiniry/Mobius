package annot.bcexpression;

import annot.bcclass.BCClass;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents <code>'this'</code> expression.
 * One <code>THIS</code> per class.
 * 
 * @author tomekb
 */
public class THIS extends OldExpression {

	/**
	 * BCClass this expression represents.
	 */
	private BCClass bcc;
	
	/**
	 * A construcotr for BCClass initialization only. Later,
	 * use {@link BCClass#getTHIS()} instead.
	 * 
	 * @param bcc - initializing class.
	 */
	public THIS(boolean isOld, BCClass bcc) {
		super(isOld);
		this.bcc = bcc;
	}

	@Override
	protected JavaType1 checkType1() {
		return getType();
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
		return "this";
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		throw new ReadAttributeException("'read' method" +
			" unavaliable, use BCClass#getTHIS() instead.");
	}

	@Override
	public String toString() {
		return "this";
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.THIS); //TODO update
	}

}
