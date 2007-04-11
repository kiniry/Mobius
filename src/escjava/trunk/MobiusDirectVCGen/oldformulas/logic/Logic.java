package mobius.directVCGen.formula.logic;

import java.util.Vector;

import mobius.directVCGen.formula.IFormula;
import mobius.directVCGen.formula.expression.Expression;
import mobius.directVCGen.formula.expression.Variable;
import mobius.directVCGen.formula.type.Type;


/**
 * This class is a library containing all the methods to create logic
 * formulas.
 * @author J. Charles
 */
public class Logic {
	/** the false of type prop */
	public static final ALogic FALSE = new False();	
	/** the true of type prop */
	public static final ALogic TRUE = new True();
	
	/**
	 * Create a And in the prop territory, from 2 booleans or
	 * 2 properties. The 2 arguments should not have different types
	 * or bad types (other than prop).
	 * @param f1 The first argument of the and, of type Prop
	 * @param f2 The second argument of the and, of type Prop
	 * @return a newly created and connector
	 */
	public static ALogic and(IFormula f1, IFormula f2) {
		if((f1.getType() != f2.getType() && f1.getType() != Type.prop))
			throw new IllegalArgumentException("Bad type when creating and, " +
					"found: " + f1.getType() + " and " + f2.getType());
		return new And(f1, f2);
	}
	
	/**
	 * Create a BoolProp object, a conversion from a boolean object
	 * to a property object.
	 * @param e the boolean object to convert
	 * @return the BoolProp conversion object
	 */
	public static ALogic boolToProp(IFormula e) {
		if(e.getType() != Type.bool)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + e.getType());
		return new BoolProp(e);
		
	}
	
	/**
	 * Create an equals object; it has 2 arguments, and
	 * they must have the same type.
	 * @param f1 the left argument
	 * @param f2 the right argument
	 * @return an equal object
	 */
	public static ALogic equals(IFormula f1, IFormula f2) {
		if(f1.getType() != f2.getType())
			throw new IllegalArgumentException("Different types when creating equals, " +
					"found: " + f1.getType() + " and " + f2.getType());

		return new Equals(f1, f2);
	}
	
	/**
	 * Create an object representing a logical implies.
	 * @param f1 the first element of the implies
	 * @param f2 the second element of the implies
	 * @return a nicely created implies
	 */
	public static ALogic implies(IFormula f1, IFormula f2) {
		if((f1.getType() != f2.getType() && f1.getType() != Type.prop))
			throw new IllegalArgumentException("Bad type when creating the implies, " +
					"found: " + f1.getType() + " and " + f2.getType());

		return new Implies(f1, f2);
	}
	
	/**
	 * Create an object representing an Or.
	 * @param f1 the left parameter of the or
	 * @param f2 the right parameter of the or
	 * @return the newly created object
	 */
	public static ALogic or(IFormula f1, IFormula f2) {
		if((f1.getType() != f2.getType() && f1.getType() != Type.prop))
			throw new IllegalArgumentException("Bad type when creating or, " +
					"found: " + f1.getType() + " and " + f2.getType());
		return new Or(f1, f2);
	}
	
	/**
	 * Creates and returns the negation of a formula
	 * @param f the formula to negate (of type prop)
	 * @return return the new not construct
	 */
	public static ALogic not(IFormula f) {
		if(f.getType() != Type.prop)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + f.getType());
		return new Not(f);
	}
	
	/**
	 * Creates a forall binding only one variable from the formula f.
	 * @param v the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static ALogic forall(Variable v, IFormula f) {
		if(f.getType() != Type.prop)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + f.getType());
		return new ForAll(v, f);
	}
	
	/**
	 * Creates a forall binding a list of variables to the formula given
	 * as an argument
	 * @param v the list of variables to bind
	 * @param f the body of the forall
	 * @return the newly created forall
	 */
	public static ALogic forall(Vector<Variable> v, IFormula f) {
		if(f.getType() != Type.prop)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + f.getType());
		return new ForAll(v, f);
	}

	/**
	 * Creates an exists binding only one variable from the formula f.
	 * @param v the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static ALogic exists(Variable v, IFormula f) {
		if(f.getType() != Type.prop)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + f.getType());
		return new Exists(v, f);
	}
	
	/**
	 * Creates a exists binding a list of variables to the formula given
	 * as an argument
	 * @param v the list of variables to bind
	 * @param f the body of the forall
	 * @return the newly created forall
	 */
	public static ALogic exists(Vector<Variable> v, IFormula f) {
		if(f.getType() != Type.prop)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + f.getType());
		return new Exists(v, f);
	}
	
	/**
	 * Main for testing purpose.
	 * @param args ignored
	 */
	public static void main(String [] args) {
		Vector<Variable> vars = new Vector<Variable>();
		Variable v1 = Expression.var("v1", Type.prop);
		Variable v2 = Expression.var("v2", Type.bool);
		vars.add(v1);
		
		IFormula formula = 
			 Logic.forall(vars, Logic.implies(v1, v2));
		System.out.println(formula);
		System.out.println(formula.subst(v2,
				Logic.implies(Logic.boolToProp(v2), 
						Logic.FALSE)));
	}

}
