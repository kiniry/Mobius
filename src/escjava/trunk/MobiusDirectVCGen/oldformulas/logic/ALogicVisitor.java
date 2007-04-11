package mobius.directVCGen.formula.logic;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.expression.AExpressionVisitor;

/**
 * A basic implementation of the part of a visitor to visit 
 * all the logic constructs.
 * @author J. Charles
 */
public abstract class ALogicVisitor extends AExpressionVisitor 
		implements ILogicVisitor {
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitAnd(mobius.directVCGen.formula.logic.And)
	 */
	public void visitAnd(And a) throws FormulaException {
		visitChildren(a);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitEquals(mobius.directVCGen.formula.logic.Equals)
	 */
	public void visitEquals(Equals e) throws FormulaException {
		visitChildren(e);		
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitFalse(mobius.directVCGen.formula.logic.False)
	 */
	public void visitFalse(False f) throws FormulaException {
		visitChildren(f);		
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitForAll(mobius.directVCGen.formula.logic.ForAll)
	 */
	public void visitForAll(ForAll f) throws FormulaException {
		visitChildren(f);		
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitExists(mobius.directVCGen.formula.logic.Exists)
	 */
	public void visitExists(Exists f) throws FormulaException {
		visitChildren(f);		
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitImplies(mobius.directVCGen.formula.logic.Implies)
	 */
	public void visitImplies(Implies i) throws FormulaException {
		visitChildren(i);		
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitOr(mobius.directVCGen.formula.logic.Or)
	 */
	public void visitOr(Or o) throws FormulaException {
		visitChildren(o);		
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitTrue(mobius.directVCGen.formula.logic.True)
	 */
	public void visitTrue(True i) throws FormulaException {
		visitChildren(i);		
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitBoolProp(mobius.directVCGen.formula.logic.BoolProp)
	 */
	public void visitBoolProp(BoolProp v) throws FormulaException {
		visitChildren(v);
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ILogicVisitor#visitNot(mobius.directVCGen.formula.logic.Not)
	 */
	public void visitNot(Not n) throws FormulaException {
		visitChildren(n);
	}

}
