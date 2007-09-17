package annot.formula;

import annot.bcexpression.BCExpression;
import annot.bcexpression.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.Priorities;

public class Predicate2Ar extends AbstractFormula {

	public Predicate2Ar(AttributeReader ar, int root)
			throws ReadAttributeException {
		super(ar, root);
	}

	public Predicate2Ar(int connector, BCExpression left, BCExpression right) {
		super(connector, left, right);
	}

	public String printRoot() {
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

	@Override
	public String printCode1(BMLConfig conf) {
		return getSubExpr(0).printCode(conf) + printRoot()
				+ getSubExpr(1).printCode(conf);
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		setSubExprCount(2);
		setSubExpr(0, ar.readExpression());
		setSubExpr(1, ar.readExpression());
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
			return printRoot() + getSubExpr(0).toString();
		} else {
			return getSubExpr(0).toString() + printRoot() + getSubExpr(1).toString();
		}
	}

	@Override
	public JavaType getType1() {
		for (int i = 0; i < getSubExprCount(); i++)
			if (getSubExpr(i).getType() != JavaType.JavaInt)
				return null;
		return JavaType.JavaBool;
	}

}
