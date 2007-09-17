package annot.formula;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

public class Formula extends AbstractFormula {

	protected Formula() {
		super();
	}

	public Formula(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
	}

	public Formula(int connector, BCExpression subExpr) {
		super(connector, subExpr);
	}

	public Formula(int connector) {
		super(connector);
	}

	public Formula(AttributeReader ar, int root) throws ReadAttributeException {
		super(ar, root);
	}

	public String printRoot(BMLConfig conf) {
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

	@Override
	public String printCode1(BMLConfig conf) {
		if (getSubExprCount() == 1)
			return printRoot(conf) + getSubExpr(0).printCode(conf);
		return getSubExpr(0).printCode(conf) + printRoot(conf)
				+ getSubExpr(1).printCode(conf);
	}

	@Override
	public void read(AttributeReader ar, int root)
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

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(getConnector());
		writeSubExpressions(aw);
	}

	@Override
	public int getPriority() {
		return Priorities.getPriority(getConnector());
	}

	@Override
	public void init() {
	}

	@Override
	public String toString() {
		if (getSubExprCount() == 1) {
			return printRoot(null) + getSubExpr(0).toString();
		} else {
			return getSubExpr(0).toString() + printRoot(null)
					+ getSubExpr(1).toString();
		}
	}

	@Override
	public JavaType getType1() {
		for (int i = 0; i < getSubExprCount(); i++)
			if (getSubExpr(i).getType() != JavaType.JavaBool)
				return null;
		return JavaType.JavaBool;
	}

}
