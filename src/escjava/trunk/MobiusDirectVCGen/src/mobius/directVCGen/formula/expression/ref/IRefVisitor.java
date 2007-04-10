package mobius.directVCGen.formula.expression.ref;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.numfloat.IFloatVisitor;

public interface IRefVisitor extends IFloatVisitor {
	public void visitRNull(RNull na) throws FormulaException;
}
