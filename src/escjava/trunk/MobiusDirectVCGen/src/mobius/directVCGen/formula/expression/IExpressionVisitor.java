package mobius.directVCGen.formula.expression;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.numfloat.IFloatVisitor;

public interface IExpressionVisitor extends IFloatVisitor{
	public void visitVariable(Variable v) throws FormulaException;

}
