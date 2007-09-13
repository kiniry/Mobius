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
		switch (connector) {
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
		if (subExpr.length == 1)
			return printRoot(conf) + subExpr[0].printCode(conf);
		return subExpr[0].printCode(conf) + printRoot(conf)
				+ subExpr[1].printCode(conf);
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		if (root == Code.NOT) {
			subExpr = new BCExpression[1];
			subExpr[0] = ar.readExpression();
		} else {
			subExpr = new BCExpression[2];
			subExpr[0] = ar.readExpression();
			subExpr[1] = ar.readExpression();
		}
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(connector);
		writeSubExpressions(aw);
	}

	@Override
	public int getPriority() {
		return Priorities.getPriority(connector);
	}

	@Override
	public void init() {
	}

	@Override
	public String toString() {
		if (subExpr.length == 1) {
			return printRoot(null) + subExpr[0].toString();
		} else {
			return subExpr[0].toString() + printRoot(null)
					+ subExpr[1].toString();
		}
	}

	@Override
	public JavaType getType1() {
		for (int i = 0; i < subExpr.length; i++)
			if (subExpr[i].getType() != JavaType.JavaBool)
				return null;
		return JavaType.JavaBool;
	}

}
