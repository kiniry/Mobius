package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents array modification specificatoin.
 * 
 * @author tomekb
 */
public class ModifiesArray extends ModifyExpression {

	/**
	 * A standard constructor.
	 * 
	 * @param me - an array variable,
	 * @param sa - specifies which array's elements can be
	 * 		modified.
	 */
	public ModifiesArray(ModifyExpression me, SpecArray sa) {
		super(Code.MODIFIES_ARRAY, me, sa);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type of this expression, should be
	 * 		{@link Code#MODIFIES_ARRAY}.
	 * @throws ReadAttributeException - if root + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		ModifyArrayExpression.
	 */
	public ModifiesArray(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf)
			+ "[" + getSubExpr(1).printRawCode(conf) + "]";
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(2);
		BCExpression array = ar.readModifyExpression();
		BCExpression index = ar.readSpecArray();
		setSubExpr(0, array);
		setSubExpr(1, index);
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString()
			+ getSubExpr(1).toString();
	}

}
