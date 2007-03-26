package mobius.directVCGen.formula.expression;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.num.INumVisitor;

public interface IExpressionVisitor extends INumVisitor{
	public void visitVariable(Variable v) throws FormulaException;

}
