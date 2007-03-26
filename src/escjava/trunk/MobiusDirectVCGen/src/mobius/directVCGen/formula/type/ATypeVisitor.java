package mobius.directVCGen.formula.type;

import mobius.directVCGen.formula.AFormulaVisitor;

public abstract class ATypeVisitor extends AFormulaVisitor 
	implements ITypeVisitor {
	
	public void visitFType(FunType type) { }
	
	public void visitType(Type type) { }
}
