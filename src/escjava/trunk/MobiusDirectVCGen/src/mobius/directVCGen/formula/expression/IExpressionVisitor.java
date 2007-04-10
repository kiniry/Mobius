package mobius.directVCGen.formula.expression;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.ref.IRefVisitor;

public interface IExpressionVisitor extends IRefVisitor{
	public void visitVariable(Variable v) throws FormulaException;

}
