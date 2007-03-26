package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;


/**
 * A formula which represents a conversion from bool to prop.
 * Generally it can be interpreted as (param = true) where param
 * is the formula contained in the construct.
 * @author J. Charles
 */
public class BoolProp extends ALogic {
	
	/**
	 * Construct a conversion from a formula of type bool.
	 * @param f The formula to convert.
	 */
	BoolProp(IFormula f) {
		add(f);
	}

	/**
	 * Construct a conversion from a list of arguments.
	 * @param args the list of arguments.
	 */
	private BoolProp(Vector<IFormula> args) {
		super(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitBoolProp(this);
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	public IFormula clone(Vector<IFormula> args) {
		return new BoolProp(args);
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		return formatWithType("((Prop) "+ get(0).toString() + ")");
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return pBoolProp;
	}
}
