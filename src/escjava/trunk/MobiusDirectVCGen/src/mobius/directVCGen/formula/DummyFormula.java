/**
 * 
 */
package mobius.directVCGen.formula;

import java.util.Vector;

import mobius.directVCGen.formula.type.Type;

/**
 * Dummy formulas are a basic (but <b>really</b> basic) implementation
 * of formulas. They have the ID dummy, i.e. 0. The type of the formula is
 * {@link Type#undef}.
 * @author J. Charles
 */
public class DummyFormula extends AFormula {

	/**
	 * Build a dummy formula from its arguments.
	 * The arguments are its children.
	 * @param args
	 */
	public DummyFormula(Vector<IFormula> args) {
		super(Type.undef, args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	@Override
	public IFormula clone(Vector<IFormula> args) {
		return new DummyFormula(args);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitDummyFormula(this);
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return dummy;
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		String res = "dummy (";
		for (IFormula f: this) {
			res += " " + f;
		}
		return res + ")";
	}
}