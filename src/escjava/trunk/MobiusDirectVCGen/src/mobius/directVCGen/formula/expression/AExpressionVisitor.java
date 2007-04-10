package mobius.directVCGen.formula.expression;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.ref.ARefVisitor;

public abstract class AExpressionVisitor extends ARefVisitor 
	implements IExpressionVisitor {
	public void visitVariable(Variable v) throws FormulaException {
		visitChildren(v);
	}
}
