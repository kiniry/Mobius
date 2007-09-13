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
		switch (connector) {
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
		return subExpr[0].printCode(conf) + printRoot()
				+ subExpr[1].printCode(conf);
	}

	@Override
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		subExpr = new BCExpression[2];
		subExpr[0] = ar.readExpression();
		subExpr[1] = ar.readExpression();
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
			return printRoot() + subExpr[0].toString();
		} else {
			return subExpr[0].toString() + printRoot() + subExpr[1].toString();
		}
	}

	@Override
	public JavaType getType1() {
		for (int i = 0; i < subExpr.length; i++)
			if (subExpr[i].getType() != JavaType.JavaInt)
				return null;
		return JavaType.JavaBool;
	}

}
