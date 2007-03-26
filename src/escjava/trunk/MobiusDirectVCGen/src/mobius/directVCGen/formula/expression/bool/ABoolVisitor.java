package mobius.directVCGen.formula.expression.bool;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.Variable;
import mobius.directVCGen.formula.type.ATypeVisitor;

public abstract class ABoolVisitor extends ATypeVisitor 
	implements IBoolVisitor {
	public void visitVariable(Variable v) throws FormulaException {
		visitChildren(v);
	}
	
	
	public void visitBAnd(BAnd and) throws FormulaException {
		visitChildren(and);
	}


	public void visitBTrue(BTrue true1) throws FormulaException { }


	public void visitBOr(BOr or) throws FormulaException {
		visitChildren(or);
	}


	public void visitBFalse(BFalse false1) throws FormulaException {}


	public void visitBImplies(BImplies implies) throws FormulaException {
		visitChildren(implies);
	}


	public void visitBEqualBool(BEqualBool bool) throws FormulaException {
		visitChildren(bool);
	}

	public void visitBEqualNum(BEqualNum num) throws FormulaException {
		visitChildren(num);
	}
	public void visitBEqualRef(BEqualRef ref) throws FormulaException {
		visitChildren(ref);
	}
	public void visitBNot(BNot ref) throws FormulaException {
		visitChildren(ref);
	}
}
