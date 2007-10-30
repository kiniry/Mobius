package annot.bcexpression.modifies;

import annot.bcexpression.BCExpression;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class describes modification of an array elements
 * from one index to another.
 * 
 * @author tomekb
 */
public class ModifiesInterval extends SpecArray {

	/**
	 * A standard constructor.
	 * 
	 * @param left - expression that evaluates to beginning
	 * 		of the changes (first affected array index).
	 * @param right - expression that evaluates to end
	 * 		of the changes (last affected array index).
	 */
	public ModifiesInterval(BCExpression from, BCExpression to) {
		super(Code.MODIFIES_INTERVAL, from, to);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type of this expression, should be
	 * 		{@link Code#MODIFIES_INTERVAL}.
	 * @throws ReadAttributeException - if root + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		array modification specification.
	 */
	public ModifiesInterval(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printRawCode(conf)
			+ " .. " + getSubExpr(1).printRawCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(2);
		BCExpression from = ar.readExpression();
		BCExpression to = ar.readExpression();
		setSubExpr(0, from);
		setSubExpr(1, to);
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString()
			+ " .. " + getSubExpr(1).toString();
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.MODIFIES_INTERVAL);
		writeSubExpressions(aw);
	}

	@Override
	protected void init() {
	}

}
