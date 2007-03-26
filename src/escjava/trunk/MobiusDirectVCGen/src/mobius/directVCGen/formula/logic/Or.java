package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;


/**
 * The class that is made to represent the logical or construct.
 * @author J. Charles
 */
public class Or extends ALogicBinary{
	/**
	 * Construct an or from its 2 parameters
	 * @param left the left element of the or
	 * @param right the right element of the or
	 */
	Or(IFormula left, IFormula right) {
		super(left, right);
	}

	/**
	 * Construct an or from a list of arguments (which has to be
	 * of side 2 to be useful...
	 * @param args the list of arguments
	 */
	private Or(Vector<IFormula> args) {
		super(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ALogicBinary#toString()
	 */
	public String toString() {
		return formatWithType(getLeft().toString() + " \\/ " 
							+ getRight().toString());
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitOr(this);
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new Or(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return pOr;
	}
}
