package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents an integer literal. Each occurence of the same literal
 * are new NumberLiteral object.
 * 
 * @author tomekb
 */
public class NumberLiteral extends AbstractIntExpression {

	/**
	 * Expression's value
	 */
	private int value;

	/**
	 * A standard constructor, used eg. by the parser.
	 * 
	 * @param literal
	 */
	public NumberLiteral(int literal) {
		super(Code.INT_LITERAL);
		this.value = literal;
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar -
	 *            stream to load from,
	 * @param root -
	 *            expression type (connector).
	 * @throws ReadAttributeException -
	 *             if stream is empty (less than 4 bytes left).
	 * @see BCExpression#BCExpression(AttributeReader, int)
	 */
	public NumberLiteral(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	/**
	 * @return String representation of it's value.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		return "" + value;
	}

	/**
	 * @return Simple String representation of this expression, for debugging
	 *         only.
	 */
	@Override
	public String toString() {
		return "" + value;
	}

	/**
	 * Reads the exression from an AttributeReader.
	 * 
	 * @param ar -
	 *            stream to load from,
	 * @param root -
	 *            connentor (unused).
	 * @throws ReadAttributeException -
	 *             if stream is empty (less than 4 bytes left).
	 */
	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		value = ar.readInt();
	}

	/**
	 * Writes this expression to AttributeWirter.
	 * 
	 * @param aw -
	 *            stream to save to.
	 */
	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(Code.INT_LITERAL);
		aw.writeInt(value);
	}

	/**
	 * Does nothing.
	 */
	@Override
	protected void init() {
	}

	/**
	 * NumberLiteral has no subexpressions, so it has the highest priority.
	 * 
	 * @return priority of this expression (from annot.textio.Priorities).
	 */
	@Override
	protected int getPriority() {
		return Priorities.LEAF;
	}

	/**
	 * @return JavaType of this expression, that is, JavaInt.
	 */
	@Override
	protected JavaType1 checkType1() {
		return JavaBasicType.JavaInt;
	}

}
