package mobius.directVCGen.formula.type;

import mobius.directVCGen.formula.FormulaException;

public interface ITypeVisitor {
	public void visitFType(FunType type) throws FormulaException ;
	public void visitType(Type type) throws FormulaException ;

}
