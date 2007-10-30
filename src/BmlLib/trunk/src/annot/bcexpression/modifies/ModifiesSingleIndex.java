package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class describes modification of single element
 * of an array.
 * 
 * @author tomekb
 */
public class ModifiesSingleIndex extends SpecArray {

	/**
	 * A standard constructor.
	 * 
	 * @param index - expression that evaluates to the
	 * 		modifies index.
	 */
	public ModifiesSingleIndex(BCExpression index) {
		super(Code.MODIFIES_SINGLE_INDEX, index);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type of this expression, should be
	 * 		{@link Code#MODIFIES_SINGLE_INDEX}.
	 * @throws ReadAttributeException - if root + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		array modification specification.
	 */
	public ModifiesSingleIndex(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printRawCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(1);
		BCExpression index = ar.readExpression();
		setSubExpr(0, index);
	}

	@Override
	public String toString() {
		return "[" + getSubExpr(0).toString() + "]";
	}

}
