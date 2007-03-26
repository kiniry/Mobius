package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;


/**
 * Construct a logical implies. (You know... a prop...)
 * @author J. Charles
 */
public class Implies extends ALogicBinary{
	/**
	 * Construct an implies from its 2 arguments.
	 * @param left the left parameter
	 * @param right the right parameter
	 */
	Implies(IFormula left, IFormula right) {
		super(left, right);
	}

	/**
	 * Construct the implies from a list of arguments. Only the first
	 * 2 are relevant.
	 * @param args the list of arguments
	 */
	private Implies(Vector<IFormula> args) {
		super(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ALogicBinary#toString()
	 */
	public String toString() {
		return formatWithType(getLeft().toString() + " -> " 
							+ getRight().toString());
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitImplies(this);
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new Implies(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return pImplies;
	}
}
