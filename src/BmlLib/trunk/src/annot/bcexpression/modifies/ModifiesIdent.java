package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents modification of a single variable
 * (local variable or field).
 * 
 * @author tomekb
 */
public class ModifiesIdent extends ModifyExpression {

	/**
	 * A standard constructor.
	 * 
	 * @param expr - expression whose modification this
	 * 		modify expression will describe. Should be
	 * 		a variable (eg. local variable or field).
	 */
	public ModifiesIdent(BCExpression expr) {
		super(Code.MODIFIES_IDENT, expr);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar input stream to load from,
	 * @param root - type of this expression, should be
	 * 		{@link Code#MODIFIES_DOT}.
	 * @throws ReadAttributeException - if stream in
	 * <code>ar</code> doesn't represent correct exrpession.
	 */
	public ModifiesIdent(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(1);
		BCExpression expr = ar.readExpression();
		setSubExpr(0, expr);
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString();
	}

}
