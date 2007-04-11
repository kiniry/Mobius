package mobius.directVCGen.formula;


/**
 * The basic class to build a visitor; with a single method
 * in order to visit the children.
 * @author J. Charles
 */
public abstract class AFormulaVisitor implements IFormulaVisitor {
	
	/**
	 * Visit all the children of a given formula.
	 * @param f the formula which must be visited...
	 */
	public void visitChildren (IFormula f) throws FormulaException {
		for (IFormula child: f) {
			child.accept(this);
		}
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormulaVisitor#visitDummyFormula(mobius.directVCGen.formula.IFormula)
	 */
	public void visitDummyFormula(IFormula df) throws FormulaException {
		visitChildren(df);
	}

}
