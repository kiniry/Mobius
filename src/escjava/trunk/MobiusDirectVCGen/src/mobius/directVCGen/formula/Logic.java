package mobius.directVCGen.formula;


import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.Term;

public class Logic {
	/** 
	 * The true of type prop 
	 */
	public static Term True() {
		return Formula.lf.mkPredLiteral(true);
	}

	/** 
	 * The false of type prop 
	 */
	public static Term False() {
		return Formula.lf.mkPredLiteral(false);
	}

	/**
	 * Create a And in the prop territory, from 2 booleans or
	 * 2 properties. The 2 arguments should not have different types
	 * or bad types (other than prop).
	 * @param f1 The first argument of the and, of type Prop
	 * @param f2 The second argument of the and, of type Prop
	 * @return a newly created and connector
	 */
	public static Term and(Term f1, Term f2) {
		if((f1.getSort() != Formula.lf.sortPred && f2.getSort() != Formula.lf.sortPred))
			throw new IllegalArgumentException("Bad type when creating and, " +
					"found: " + f1.getSort() + " and " + f2.getSort());
		return Formula.lf.mkFnTerm(Formula.lf.symAnd, new Term[]{f1, f2});
	}
	
	/**
	 * Create a BoolProp object, a conversion from a boolean object
	 * to a property object.
	 * @param e the boolean object to convert
	 * @return the BoolProp conversion object
	 */
	public static Term boolToProp(Term e) {
		if(e.getSort() != Formula.lf.sortBool)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + e.getSort());
		return Formula.lf.mkFnTerm(Formula.lf.symIsTrue, new Term[] {e});
		
	}
	
	/**
	 * Create an equals object; it has 2 arguments, and
	 * they must have the same type.
	 * @param f1 the left argument
	 * @param f2 the right argument
	 * @return an equal object
	 */
	public static Term equals(Term f1, Term f2) {
		if(f1.getSort() != f2.getSort())
			throw new IllegalArgumentException("Different types when creating equals, " +
					"found: " + f1.getSort() + " and " + f2.getSort());

		return  Formula.lf.mkFnTerm(Formula.lf.symAnyEQ, new Term[]{f1, f2});
	}
	
	/**
	 * Create an object representing a logical implies.
	 * @param f1 the first element of the implies
	 * @param f2 the second element of the implies
	 * @return a nicely created implies
	 */
	public static Term implies(Term f1, Term f2) {
		if((f1.getSort() != f2.getSort() && f1.getSort() != Formula.lf.sortPred))
			throw new IllegalArgumentException("Bad type when creating the implies, " +
					"found: " + f1.getSort() + " and " + f2.getSort());

		return Formula.lf.mkFnTerm(Formula.lf.symImplies, new Term[]{f1, f2});
	}
	
	/**
	 * Create an object representing an Or.
	 * @param f1 the left parameter of the or
	 * @param f2 the right parameter of the or
	 * @return the newly created object
	 */
	public static Term or(Term f1, Term f2) {
		if((f1.getSort() != f2.getSort() && f1.getSort() != Formula.lf.sortPred))
			throw new IllegalArgumentException("Bad type when creating or, " +
					"found: " + f1.getSort() + " and " + f2.getSort());

		return Formula.lf.mkFnTerm(Formula.lf.symOr, new Term[]{f1, f2});
	}
	
	
	/**
	 * Creates and returns the negation of a formula
	 * @param f the formula to negate (of type prop)
	 * @return return the new not construct
	 */
	public static Term not(Term f) {
		if(f.getSort() != Formula.lf.sortPred)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + f.getSort());
		return Formula.lf.mkFnTerm(Formula.lf.symNot, new Term []{f});
	}
	
	/**
	 * Creates a forall binding only one variable from the formula f.
	 * @param v the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static QuantTerm forall(QuantVariable v, Term f) {
	
		if(f.getSort() != Formula.lf.sortPred)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + f.getSort());
		
		return Formula.lf.mkQuantTerm(true, new QuantVariable [] {v}, f, null, null);
	}
	

	
	/**
	 * Creates an exists binding only one variable from the formula f.
	 * @param v the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static QuantTerm exists(QuantVariable v, Term f) {
	
		if(f.getSort() != Formula.lf.sortPred)
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
				"found: " + f.getSort());
		
		return Formula.lf.mkQuantTerm(false, new QuantVariable [] {v}, f, null, null);
	}	
		


	
	public static FnTerm typeLE(Term t1, Term t2) {
		return Formula.lf.mkFnTerm(Formula.lf.symTypeLE, new Term[] {t1, t2});
	}
	
	/**
	 * Main for testing purpose.
	 * @param args ignored
	 */
	public static void main(String [] args) {
//		Vector<Variable> vars = new Vector<Variable>();
//		Variable v1 = Expression.var("v1", Type.prop);
//		Variable v2 = Expression.var("v2", Type.bool);
//		vars.add(v1);
//		
//		IFormula formula = 
//			 Logic.forall(vars, Logic.implies(v1, v2));
//		System.out.println(formula);
//		System.out.println(formula.subst(v2,
//				Logic.implies(Logic.boolToProp(v2), 
//						Logic.FALSE)));
		System.out.println(Logic.and(Logic.True(), Logic.False()));
	}
}
