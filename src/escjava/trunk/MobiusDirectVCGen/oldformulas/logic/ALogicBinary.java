package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.IFormula;


/**
 * This class represents a logical binary (with left and right) formula.
 * The formula is of type prop and has only 2 children.
 * @author J. Charles
 */
public abstract class ALogicBinary extends ALogic {

	/**
	 * Construct a binary logic formula. It has 2 arguments,
	 * left and right.
	 * @param left the left paramater of the binary formula
	 * @param right the right parameter of the binary formula
	 */
	ALogicBinary(IFormula left, IFormula right) {
		add(left);
		add(right);
	}
	
	/**
	 * Build a binary formula from a list of args.
	 * @param args The list of parameters (its size must be 2)
	 */
	public ALogicBinary(Vector<IFormula> args) {
		super(args);
		if(args.size() != 2) {
			throw new IllegalArgumentException("args.size() != 2");
		}
	}

	/**
	 * Returns the left element of the formula.
	 * @return a formula
	 */
	public IFormula getLeft() {
		return get(0);
	}
	
	/**
	 * Returns the right element of the formula.
	 * @return a formula
	 */
	public IFormula getRight() {
		return get(1);
	}
	
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return formatWithType (getLeft().toString() + ", " + getRight().toString());
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ALogic#formatWithType(java.lang.String)
	 */
	public String formatWithType(String mid) {
		return "(" + mid + "):" + getType();
	}


}
