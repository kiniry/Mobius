package mobius.directVCGen.formula.expression;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.numfloat.AFloatVisitor;

public abstract class AExpressionVisitor extends AFloatVisitor 
	implements IExpressionVisitor {
	public void visitVariable(Variable v) throws FormulaException {
		visitChildren(v);
	}
}
