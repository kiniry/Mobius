package annot.bcexpression;

import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

public class ArithmeticExpression extends AbstractIntExpression {

	public ArithmeticExpression(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	public ArithmeticExpression(int connector, BCExpression left,
			BCExpression right) {
		super(connector, left, right);
	}

	public ArithmeticExpression(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	@Override
	protected int getPriority() {
		return Priorities.getPriority(getConnector());
	}

	@Override
	protected JavaBasicType getType1() {
		if ((getSubExpr(0).getType() != JavaBasicType.JavaInt)
			|| (getSubExpr(1).getType() != JavaBasicType.JavaInt))
				return null;
		return JavaBasicType.JavaInt;
	}

	@Override
	protected void init() {
	}

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
