package mobius.directVCGen.formula;

import mobius.directVCGen.formula.logic.ILogicVisitor;

/**
 * The interface representing the visitor to use with the formulas.
 * @author J. Charles
 */
public interface IFormulaVisitor extends ILogicVisitor {
	/**
	 * Visit the dummy formulas. In fact dummy formulas are simple 
	 * instanciations of the abstract type {@link mobius.directVCGen.formula.IFormula},
	 * hence the type of the parameter which is {@link mobius.directVCGen.formula.IFormula} and not
	 * {@link mobius.directVCGen.formula.DummyFormula}.
	 * @param df the DummyFormula to inspect
	 * @throws FormulaException if there was an error somewhere.
	 */
	public void visitDummyFormula(IFormula df) throws FormulaException;
}
