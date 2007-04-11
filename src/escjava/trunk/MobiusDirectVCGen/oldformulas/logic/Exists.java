package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.Variable;


/**
 * Represents an exists construct: it behaves more or less
 * like a forall.
 * @author J. Charles
 */
public class Exists extends ForAll {
	/**
	 * A constructor to build an exists from a single variable
	 * and a formula.
	 * @param var The variable to bind
	 * @param f the formula in which to bind the variable
	 */
	Exists(Variable var, IFormula f) {
		this(new Vector<Variable>(), f);
		getVars().add(var);
	}
	
	/**
	 * A constructor to build an exists from several variables
	 * and a formula.
	 * @param vars The variables to bind
	 * @param f the formula in which to bind the variables
	 */
	Exists(Vector<Variable> vars, IFormula f) {
		this(vars, new Vector<IFormula>());
		add(f);
	}

	/**
	 * Build an exists from several variables as well as a list of 
	 * arguments. Only the first element of the list is relevant.
	 * @param vars the variables to bind
	 * @param args the formula to which bind the variable
	 */
	protected Exists(Vector<Variable> vars, Vector<IFormula> args) {
		super(vars, args);
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.logic.ForAll#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitExists(this);
	}
	

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	public IFormula clone(Vector<IFormula> args) {
		return new Exists(new Vector<Variable> (getVars()), args);
	}
	

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		String res = "exists";
		for (Variable v : getVars()) {
			res += " " + v;
		}
		res += ", " + get(0);
		return res;
	}

}
