package mobius.directVCGen.formula.expression.num;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.bool.IBoolVisitor;

public interface INumVisitor extends IBoolVisitor {
	public void visitNAdd(NAdd na) throws FormulaException;
	public void visitNInt(NInt ni) throws FormulaException;
	public void visitNByte(NByte nb) throws FormulaException;
	public void visitNShort(NShort ns) throws FormulaException;
	public void visitNLong(NLong nl) throws FormulaException;
	public void visitNMinus(NMinus nm) throws FormulaException;
	public void visitNMod(NMod nm) throws FormulaException;
	public void visitNMult(NMult nm) throws FormulaException;
	public void visitNSub(NSub ns) throws FormulaException;
}
