package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;


/**
 * This class represents a not construct, for the properties.
 * @author J. Charles
 */
public class Not extends ALogic {
	
	/**
	 * Construct the negation of the formula passed as an argument.
	 * @param f the formula to negate
	 */
	Not(IFormula f) {
		add(f);
	}

	/**
	 * Construct the not from the given list of arguments.
	 * Only the first element of the list is relevant.
	 * @param args the list of arguments
	 */
	private Not(Vector<IFormula> args) {
		super(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitNot(this);
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	public IFormula clone(Vector<IFormula> args) {
		return new Not(args);
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return formatWithType("not " + get(0).toString());
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return pNot;
	}
}
