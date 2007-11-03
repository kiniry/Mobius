package annot.formula;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaBasicType;
import annot.bcexpression.JavaType1;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents binary predicate of boolean return
 * type and integer subexpressions return types.
 * 
 * @author tomekb
 */
public class Predicate2Ar extends AbstractFormula {

	/**
	 * A standard constructor, used eg. in parser.
	 * 
	 * @param connector - type of predicate (connector),
	 * @param left - left subexpression,
	 * @param right - right subexpression.
	 */
	public Predicate2Ar(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - stream to load from,
	 * @param root - type of predicate (connector),
	 * @throws ReadAttributeException - if connector + stream
	 * 		in AttributeReader don't represents correct
	 * 		binary predicate.
	 * @see AbstractFormula#AbstractFormula(AttributeReader, int)
	 */
	public Predicate2Ar(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	/**
	 * @return String representation of predicate's connector.
	 */
	private String printRoot() {
		switch (getConnector()) {
		case Code.GRT:
			return " > ";
		case Code.GRTEQ:
			return " >= ";
		case Code.LESS:
			return " < ";
		case Code.LESSEQ:
			return " <= ";
		case Code.EQ:
			return " == ";
		case Code.NOTEQ:
			return " != ";
		default:
			return "??";
		}
	}

	/**
	 * Prints this predicate to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of this predicate,
	 * 		without (block marks (used for line-breaking
	 * 		by prettyPrinter) and parenthness) at root.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf) + printRoot()
				+ getSubExpr(1).printCode(conf);
	}

	/**
	 * @return Simple String representation of this
	 * 		predicate, for debugging only.
	 */
	@Override
	public String toString() {
		if (getSubExprCount() == 1) {
			return printRoot() + getSubExpr(0).toString();
		} else {
			return getSubExpr(0).toString() + printRoot()
					+ getSubExpr(1).toString();
		}
	}

	/**
	 * Reads the predicate from an AttributeReader (except
	 * connector, thar has been already read and set).
	 * 
	 * @param ar - stream to load from,
	 * @param root - connentor.
	 * @throws ReadAttributeException - if connector + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		binary predicate.
	 */
	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(2);
		setSubExpr(0, ar.readExpression());
		setSubExpr(1, ar.readExpression());
	}

	/**
	 * @return priority of this expression
	 * 		(from annot.textio.Priorities).
	 */
	@Override
	protected int getPriority() {
		return Priorities.getPriority(getConnector());
	}

	/**
	 * Checks if all subexpressions have correct types
	 * and return type of this predicate.
	 * 
	 * @return JavaBool, or null if it's invalid
	 * 		(if one of it's subexpression have wrong type
	 * 		or is invalid).
	 */
	@Override
	protected JavaType1 checkType1() {
		if (getSubExpr(0).getType().compareTypes(
			getSubExpr(1).getType())
			== JavaType1.TYPES_UNRELATED)
				return null;
		if ((getConnector() != Code.EQ) && (getConnector() != Code.NOTEQ))
			if (getSubExpr(0).getType() != JavaBasicType.JavaInt)
				return null;
		return JavaBasicType.JavaBool;
	}

}
