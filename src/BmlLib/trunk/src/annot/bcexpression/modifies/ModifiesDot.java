package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldAccess;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents {@link FieldAccess}
 * as a {@link ModifyExpression} (modifiyExpression in form:
 * modifyExpression . expression,
 * where expression should be a variable.
 * 
 * @author tomekb
 */
public class ModifiesDot extends ModifyExpression {

	/**
	 * A standard construcotr.
	 * 
	 * @param left - left subexpression (may contain dots),
	 * @param right - right subexpression, without dots
	 * 		nor arrays.
	 */
	public ModifiesDot(ModifyExpression left, BCExpression right) {
		super(Code.MODIFIES_DOT, left, right);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type of this expression, should be
	 * 		{@link Code#MODIFIES_DOT}.
	 * @throws ReadAttributeException - if root + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		ModifyExpression.
	 */
	public ModifiesDot(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf)
			+ "." + getSubExpr(1).printCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(2);
		ModifyExpression left = ar.readModifyExpression();
		BCExpression right = ar.readExpression();
		setSubExpr(0, left);
		setSubExpr(1, right);
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString()
			+ "." + getSubExpr(1).toString();
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.MODIFIES_DOT);
		writeSubExpressions(aw);
	}

	@Override
	protected void init() {}

}
