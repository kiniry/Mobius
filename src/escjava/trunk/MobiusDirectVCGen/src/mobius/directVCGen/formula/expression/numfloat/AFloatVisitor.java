package mobius.directVCGen.formula.expression.numfloat;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.num.ANumVisitor;

public abstract class AFloatVisitor extends ANumVisitor 
	    implements IFloatVisitor {

	public void visitFFloat(FFloat na) throws FormulaException {
		visitChildren(na);
	}

	public void visitFDouble(FDouble na) throws FormulaException {
		visitChildren(na);
	}
}
