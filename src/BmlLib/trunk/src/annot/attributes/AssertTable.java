package annot.attributes;

import annot.bcclass.BCMethod;
import annot.formula.AbstractFormula;
import annot.io.AttributeReader;
import annot.io.ReadAttributeException;
import annot.textio.IDisplayStyle;

public class AssertTable extends BCAttributeTable1 {

	public AssertTable(BCMethod m, BCAttributeMap parent) {
		super(m, parent);
	}

	@Override
	public String getName() {
		return IDisplayStyle.__assertTable;
	}

	@Override
	public SingleAssert loadSingle(BCMethod m, AttributeReader ar)
			throws ReadAttributeException {
		AbstractFormula f = (AbstractFormula) ar.readExpression();
		SingleAssert sa = new SingleAssert(m, null, -1, f);
		return sa;
	}

	@Override
	public int singleType() {
		return AType.C_ASSERT;
	}

}
