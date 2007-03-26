package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;


/**
 * Represents a logical True. Therefore it has the type prop.
 * @author J. Charles
 */
public class True extends ALogic {

	/**
	 * Construct a True constant.
	 */
	True() {
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitTrue(this);
	}

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return "True";
		
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return this;
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return pTrue;
	}
}
