package mobius.directVCGen.formula.expression.bool;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.type.ITypeVisitor;

public interface IBoolVisitor extends ITypeVisitor{
	public void visitBAnd(BAnd and) throws FormulaException;
	public void visitBTrue(BTrue true1) throws FormulaException;
	public void visitBOr(BOr or) throws FormulaException;
	public void visitBFalse(BFalse false1) throws FormulaException;
	public void visitBImplies(BImplies implies) throws FormulaException;
	public void visitBEqualBool(BEqualBool bool) throws FormulaException;
	public void visitBEqualNum(BEqualNum num) throws FormulaException;
	public void visitBEqualRef(BEqualRef ref) throws FormulaException;
	public void visitBNot(BNot ref) throws FormulaException;
}
