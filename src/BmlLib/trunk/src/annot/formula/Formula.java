package annot.formula;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * This class represents expression of boolean result type
 * and boolean subexpressions result types.
 * 
 * @author tomekb
 */
public class Formula extends AbstractFormula {

	/**
	 * A constructor for 0Arg formula.
	 */
	protected Formula() {
		super();
	}

	/**
	 * Another constructor for 0Arg formula.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface).
	 */
	protected Formula(int connector) {
		super(connector);
	}

	/**
	 * A Constructor for unary formula.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface),
	 * @param subExpr - subexpression.
	 */
	public Formula(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	/**
	 * A constructor for binary formula.
	 * 
	 * @param connector - type of expression
	 * 		(from annot.io.Code interface),
	 * @param left - left subexpression,
	 * @param right - right subexrpession.
	 */
	public Formula(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
	}

	/**
	 * A constructor from AttributeReader.
	 * 
	 * @param ar - stream to load from,
	 * @param root - expression type (connector).
	 * @throws ReadAttributeException - if connector + stream
	 * 		in <code>ar</code> doesn't represent any
	 * 		formula from this class.
	 * @see AbstractFormula#AbstractFormula(AttributeReader, int)
	 */
	public Formula(AttributeReader ar, int root) throws ReadAttributeException {
		super(ar, root);
	}

	/**
	 * Prints formula's connector as a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of formula's connector.
	 */
	private String printRoot(BMLConfig conf) {
		switch (getConnector()) {
		case Code.AND:
			return " && ";
		case Code.OR:
			return " || ";
		case Code.IMPLIES:
			return " ==> ";
		case Code.NOT:
			return "~";
		case Code.EQUIV:
			return " <==> ";
		case Code.NOTEQUIV:
			return " <=!=> ";
		default:
			return "??";
		}
	}

	/**
	 * Prints this formula to a String.
	 * 
	 * @param conf - see {@link BMLConfig}.
	 * @return String representation of formula,
	 * 		without (block marks (used for line-breaking
	 * 		by prettyPrinter) and parenthness) at root.
	 */
	@Override
	protected String printCode1(BMLConfig conf) {
		if (getSubExprCount() == 1)
			return printRoot(conf) + getSubExpr(0).printCode(conf);
		return getSubExpr(0).printCode(conf) + printRoot(conf)
				+ getSubExpr(1).printCode(conf);
	}

	/**
	 * @return Simple String representation of this
	 * 		formula, for debugging only.
	 */
	@Override
	public String toString() {
		if (getSubExprCount() == 1) {
			return printRoot(null) + getSubExpr(0).toString();
		} else {
			return getSubExpr(0).toString() + printRoot(null)
					+ getSubExpr(1).toString();
		}
	}

	/**
	 * Reads the formula from an AttributeReader (except
	 * connector, thar has been already read and set).
	 * 
	 * @param ar - stream to load from,
	 * @param root - connentor.
	 * @throws ReadAttributeException - if connector + stream
	 * 		in <code>ar</code> doesn't represent correct
	 * 		expression.
	 */
	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		if (root == Code.NOT) {
			setSubExprCount(1);
			setSubExpr(0, ar.readExpression());
		} else {
			setSubExprCount(2);
			setSubExpr(0, ar.readExpression());
			setSubExpr(1, ar.readExpression());
		}
	}

	/**
	 * Writes this formula to AttributeWirter.
	 * 
	 * @param aw - stream to save to.
	 */
	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(getConnector());
		writeSubExpressions(aw);
	}

	/**
	 * Does nothing.
	 */
	@Override
	protected void init() {
	}

	/**
	 * @return priority of this formula
	 * 		(from annot.textio.Priorities).
	 */
	@Override
	protected int getPriority() {
		return Priorities.getPriority(getConnector());
	}

	/**
	 * Checks if all subexpressions have correct types
	 * and return type of this formula (JavaBool).
	 * 
	 * @return JavaBool, or null if this formula is invalid
	 * 		(if one of it's	subexpression have wrong type
	 * 		or is invalid).
	 */
	@Override
	protected JavaType getType1() {
		for (int i = 0; i < getSubExprCount(); i++)
			if (getSubExpr(i).getType() != JavaType.JavaBool)
				return null;
		return JavaType.JavaBool;
	}

}
