package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;


/**
 * This class represents the and construct for the properties.
 * It has 2 parameters, both of type prop, and returns a value in prop.
 * @author J. Charles
 */
public class And extends ALogicBinary{
	/**
	 * The basic constructor, construct the and from its 2 parameters.
	 * @param left The left element in the and
	 * @param right The right element in the and
	 */
	And(IFormula left, IFormula right) {
		super(left, right);
	}

	/**
	 * An internal constructor which construct an and from the given
	 * formulas from the list.
	 * @param args the list of parameters
	 */
	private And(Vector<IFormula> args) {
		super(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ALogicBinary#toString()
	 */
	public String toString() {
		return formatWithType(getLeft().toString() + " /\\ " 
							+ getRight().toString());
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitAnd(this);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new And(args);
	}

	public int getID() {
		return pAnd;
	}

	
	
	
}
