package mobius.directVCGen.formula;

import mobius.directVCGen.formula.logic.ILogicVisitor;

/**
 * The interface representing the visitor to use with the formulas.
 * @author J. Charles
 */
public interface IFormulaVisitor extends ILogicVisitor {
	public void visitDummyFormula(DummyFormula df) throws FormulaException;
}
