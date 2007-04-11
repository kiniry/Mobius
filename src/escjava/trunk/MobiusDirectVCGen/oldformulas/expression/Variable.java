package mobius.directVCGen.formula.expression;

import java.util.Vector;

import mobius.directVCGen.formula.AFormula;
import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.type.Type;


/**
 * This class is used to represent a variable.
 * @author J. Charles
 */
public class Variable extends AFormula {
	/** the name of the variable */
	private final String fName;
	private final String fLongName;
	private final int instNum;
	
	/**
	 * The constructor take the name of the variable and its type.
	 * @param name the name of the variable (a String representation)
	 * @param t the type of the variable
	 */
	Variable(String name, Type t) {
		super(t);
		fName = name;
		instNum = 0;
		fLongName = fName + "_" + instNum;
	}
	
	
	Variable(Variable v) {
		super(v.getType());
		fName = v.fName;
		instNum = v.instNum + 1;
		fLongName = fName + "_" + instNum;
	}
	
	/**
	 * Return the name of the variable.
	 * @return the name a string representation
	 */
	public String getName() {
		return fName;
	}
	

	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		if(instNum != 0) {
			return fLongName + ":" + getType();
		} else {
			return fName + ":" + getType();
		}
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	public boolean equals(Object o) {
		return ((o instanceof Variable) &&
				o.hashCode() == this.hashCode());
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	public int hashCode() {
		return fLongName.hashCode();
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitVariable(this);
		
	}
	

	public IFormula subst(Variable v, IFormula e) {
		if(v.equals(this)) {
			return e;
		}
		else {
			return this;
		}
	}


	@Override
	public IFormula clone(Vector<IFormula> args) {
		return this;
	}


	public Variable instanciate() {
		return new Variable(this);
	}


	public int getID() {
		return eVariable;
	}
}
