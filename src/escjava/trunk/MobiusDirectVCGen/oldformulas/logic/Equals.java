package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;


/**
 * A class to represent an equality into the realm of props.
 * It can be given any variable of any type, though the 2 variables
 * should be of the same type.
 * @author J. Charles
 */
public class Equals extends ALogicBinary {

	/**
	 * Construct the equality, giving it the 2 sides.
	 * @param left the left parameter of the equality 
	 * @param right the right parameter of the equality
	 */
	Equals(IFormula left, IFormula right) {
		super(left, right);
	}

	/**
	 * An constructor which construct an equality from a list of
	 * parameters.
	 * @param args The list of equality to construct the equality from.
	 */
	private Equals(Vector<IFormula> args) {
		super(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ALogicBinary#toString()
	 */
	public String toString() {
		return formatWithType("(" + getLeft().toString() + 
				" = " + getRight().toString());
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitEquals(this);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new Equals(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return pEquals;
	}

}
