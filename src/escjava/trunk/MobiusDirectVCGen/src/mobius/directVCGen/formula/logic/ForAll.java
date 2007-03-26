package mobius.directVCGen.formula.logic;

import java.util.Iterator;
import java.util.Vector;

import mobius.directVCGen.formula.FormulaException;
import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.IFormulaVisitor;
import mobius.directVCGen.formula.expression.Variable;
import mobius.directVCGen.formula.utils.VariableGetterVisitor;


/**
 * The class to represent the foralls...
 * A forall is made of a list of variable mashed up with a single formula
 * from the prop territory. Both (the formula and the forall construct)
 * are in the prop camp.
 * @author J. Charles
 */
public class ForAll extends ALogic {
	/** the binded variables of the forall ;) */
	private final Vector<Variable> fVars;
	
	
	/**
	 * Basic constructor. Construct a forall from 1 variable
	 * and one formula.
	 * @param var The variable to bind with the forall. Cannot be null.
	 * @param f The formula contained inside the forall, of type prop.
	 * Cannot be null either.
	 */
	ForAll(Variable var, IFormula f) {
		this(new Vector<Variable>(), f);
		fVars.add(var);
	}
	
	/**
	 * Construct a forall from a list of variables and a single
	 * formula.
	 * @param vars The list of variables to bind with the forall
	 * @param f The formula contained inside the forall.
	 */
	ForAll(Vector<Variable> vars, IFormula f) {
		this(vars, new Vector<IFormula>());
		add(f);
	}

	/**
	 * A private 'generic' constructor.
	 * Takes a list of variables as well as a list of formulas.
	 * Used for convenience only.
	 * @param vars a list of variables, should not be null
	 * @param args a list of formulas, should not be null either
	 */
	protected ForAll(Vector<Variable> vars, Vector<IFormula> args) {
		super(args);
		fVars = vars;
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#accept(mobius.directVCGen.formula.IFormulaVisitor)
	 */
	public void accept(IFormulaVisitor v) throws FormulaException {
		v.visitForAll(this);
	}
	
	/**
	 * Returns an iterator to iterate on 
	 * the bounded variables of the forall.
	 * @return a valid iterator, ready to be thrown a-way
	 */
	public Iterator<Variable> variableIterator() {
		return fVars.iterator();
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#clone(java.util.Vector)
	 */
	public IFormula clone(Vector<IFormula> args) {
		return new ForAll(new Vector<Variable> (fVars), args);
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.AFormula#subst(mobius.directVCGen.formula.expression.Variable, mobius.directVCGen.formula.IFormula)
	 */
	@SuppressWarnings("unchecked")
	public IFormula subst(Variable var, IFormula expr) {
		Vector<Variable> varlist = VariableGetterVisitor.collectVars(expr);
		if(!varlist.contains(var))
			varlist.add(var);

	  	boolean bHasChanged = false;
	  	IFormula newArg = this.get(0);
	  	Vector<Variable> newFVars = (Vector<Variable>)fVars.clone();
	  	
		for(Variable v: varlist) {
			if(newFVars.contains(v)) {
				//bHasChanged = true;
				Variable newVar = v.instanciate();
				newFVars.remove(v);
				newFVars.add(newVar);
				newArg = newArg.subst(v, newVar);
			}
			
		}
		
		IFormula arg = newArg;
		newArg = newArg.subst(var, expr);
		if(arg != newArg) {
			bHasChanged = true; 
		}
		
		if(bHasChanged) {
			return new ForAll(newFVars, newArg);
		}
		return this;
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		String res = "forall";
		for (Variable v : fVars) {
			res += " " + v;
		}
		res += ", " + get(0);
		return res;
	}
	
	/**
	 * Returns the variables contained in the forall.
	 * @return a viable vector of variables
	 */
	protected Vector<Variable> getVars() {
		return fVars;
	}

	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.IFormula#getID()
	 */
	public int getID() {
		return pForAll;
	}

}
