package mobius.directVCGen.formula.expression.numfloat;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.num.INumVisitor;

public interface IFloatVisitor extends INumVisitor {
	public void visitFFloat(FFloat na) throws FormulaException;
	public void visitFDouble(FDouble na) throws FormulaException;
}
