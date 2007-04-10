package mobius.directVCGen.formula.expression.ref;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.numfloat.AFloatVisitor;

public abstract class ARefVisitor extends AFloatVisitor 
	    implements IRefVisitor {
	public void visitRNull(RNull na) throws FormulaException {
		//visitChildren(na);
	}
}
