package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

/**
 * Represents artihmetic expressions (int x int --> int),
 * including shifts and bit operations.
 * Unary arithmetic operation (unary minus) has been moved
 * to the {@link UnaryArithmeticExpression}.
 * 
 * @author tomekb
 */
public class ArithmeticExpression extends AbstractIntExpression {
//XXX should bitwise and shifts expressions be separated from arithmetic expressions?
//what is the important differecne between those expression types?

	/**
	 * A constructor for unary minus only.
	 */
	protected ArithmeticExpression(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	/**
	 * A standard constructor. 
	 * 
	 * @param connector - type of expression, from
	 * 		<code>Code</code> interface,
	 * @param left - left subexpression,
	 * @param right - right subexpression.
	 */
	public ArithmeticExpression(int connector, BCExpression left,
			BCExpression right) {
		super(connector, left, right);
	}

	/**
	 * A constructor from AttributeReader, used for loading
	 * from file (from BCEL's unknown Attribute).
	 * 
	 * @param ar - input stream to load from,
	 * @param root - type o expression (last read byte from
	 * 		<code>ar</code>.
	 * @throws ReadAttributeException - if stream
	 * 		in <code>ar</code> doesn't represent a correct
	 * 		artimethic expression.
	 * @see BCExpression#BCExpression(AttributeReader, int)
	 */
	public ArithmeticExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected int getPriority() {
		return Priorities.getPriority(getConnector());
	}

	@Override
	protected JavaType1 checkType1() {
		if ((getSubExpr(0).checkType() != JavaBasicType.JavaInt)
			|| (getSubExpr(1).checkType() != JavaBasicType.JavaInt))
				return null;
		return JavaBasicType.JavaInt;
	}

	@Override
	protected void init() {
	}

	/**
	 * @return string representation of expression's connector.
	 */
	protected String printRoot() {
		switch (getConnector()) {
		case Code.BITWISEAND: return " & ";
		case Code.BITWISEOR: return " | ";
		case Code.BITWISEXOR: return " ^ ";
		case Code.DIV: return " / ";
		case Code.MINUS: return " - ";
		case Code.MULT: return " * ";
		case Code.NEG: return " -";
		case Code.PLUS: return " + ";
		case Code.REM: return " % ";
		case Code.SHL: return " << ";
		case Code.SHR: return " >> ";
		case Code.USHR: return " >>> "; //XXX
		default: throw new RuntimeException("unknown arithmetic opcode: " + getConnector());
		}
	}
	
	@Override
	protected String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf) + printRoot()
			+ getSubExpr(1).printCode(conf);
	}

	@Override
	protected void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(2);
		BCExpression left = ar.readExpression();
		BCExpression right = ar.readExpression();
		setSubExpr(0, left);
		setSubExpr(1, right);
	}

	@Override
	public String toString() {
		return getSubExpr(0).toString() + printRoot()
			+ getSubExpr(1).toString();
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(getConnector());
		writeSubExpressions(aw);
	}

}
