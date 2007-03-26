package mobius.directVCGen.formula.expression;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.num.ANumVisitor;

public abstract class AExpressionVisitor extends ANumVisitor 
	implements IExpressionVisitor {
	public void visitVariable(Variable v) throws FormulaException {
		visitChildren(v);
	}
}
