package mobius.directVCGen.formula.expression.num;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.bool.ABoolVisitor;

public abstract class ANumVisitor extends ABoolVisitor 
	    implements INumVisitor {

	public void visitNAdd(NAdd na) throws FormulaException {
		visitChildren(na);
	}
	public void visitNInt(NInt ni) throws FormulaException {
	}
	public void visitNLong(NLong nl) throws FormulaException {
	}
	public void visitNShort(NShort ns) throws FormulaException {
	}
	public void visitNByte(NByte nb) throws FormulaException {
	}
	
	public void visitNMinus(NMinus nm) throws FormulaException {
		visitChildren(nm);
	}	
	
	public void visitNMod(NMod nm) throws FormulaException {
		visitChildren(nm);
	}
	public void visitNMult(NMult nm) throws FormulaException {
		visitChildren(nm);
	}
	public void visitNSub(NSub ns) throws FormulaException {
		visitChildren(ns);
	}
}
