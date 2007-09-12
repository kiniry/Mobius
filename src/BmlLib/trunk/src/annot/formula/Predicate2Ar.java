package annot.formula;

import annot.bcexpression.AbstractIntExpression;
import annot.bcexpression.BCExpression;
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

	@Override
	public int getPriority() {
		return Priorities.getPriority(connector);
	}

	@Override
	public String printCode1(BMLConfig conf) {
		return subExpr[0].printCode(conf) + printRoot(conf)
				+ subExpr[1].printCode(conf);
	}

	public String printRoot(BMLConfig conf) {
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
	public void read(AttributeReader ar, int root)
			throws ReadAttributeException {
		subExpr = new BCExpression[2];
		subExpr[0] = ar.readExpression();
		if (!(subExpr[0] instanceof AbstractIntExpression))
			throw new ReadAttributeException(
					"Integer expression expected, read "
							+ subExpr[0].getClass().toString());
		subExpr[1] = ar.readExpression();
		if (!(subExpr[0] instanceof AbstractIntExpression))
			throw new ReadAttributeException(
					"integer expression expected, read "
							+ subExpr[0].getClass().toString());
	}

	@Override
	public void write(AttributeWriter aw) {
		aw.writeByte(connector);
		writeSubExpressions(aw);
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

}
