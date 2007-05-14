package mobius.directVCGen.formula;


import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.PredSymbol;
import escjava.sortedProver.NodeBuilder.Sort;


// TODO: add comments
public class Logic {
	
	// TODO: add comments
	private static Term logicBinaryOp(Term f1, Term f2, PredSymbol sym){
		if((f1.getSort() != sort || f2.getSort() != sort))
			throw new IllegalArgumentException("Bad type. Expecting predicates, " +
					"found: " + f1.getSort() + " and " + f2.getSort());
		return Formula.lf.mkFnTerm(sym, new Term[]{f1, f2});
	}
	
	// TODO: add comments
	private static Term logicUnaryOp(Term f, PredSymbol sym){
		if(f.getSort() != sort)
			throw new IllegalArgumentException("Bad type. Expecting predicate, " +
				"found: " + f.getSort());
		return Formula.lf.mkFnTerm(sym, new Term []{f});
	}
	
	// TODO: add comments	
	private static Term numBinaryOp(Term l, Term r, int tag){
		if(l.getSort() != r.getSort() ||
				(!Num.isNum(l.getSort()) || !Num.isNum(r.getSort())))
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			if(r.getSort() == Num.sortReal) {
				l = Num.intToReal(l);
				t = Formula.lf.mkFnTerm(Formula.lf.symRealPred, new Term[] {l, r});
			}
			else {
				t = Formula.lf.mkFnTerm(Formula.lf.symIntPred, new Term[] {l, r});
			}
			
		}
		else if (l.getSort() == Num.sortReal) {
			if(r.getSort() == Num.sortInt) {
				r = Num.intToReal(r);
			}
			t = Formula.lf.mkFnTerm(Formula.lf.symRealPred, new Term[] {l, r});
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		t.tag = tag;
		return t;
	}
	
	
	
	/** the sort to represent the predicates */
	public static Sort sort = Formula.lf.sortPred;

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
	 * Create a BoolProp object, a conversion from a boolean object
	 * to a property object if necessary.
	 * @param e the boolean object to convert
	 * @return the BoolProp conversion object
	 */
	public static Term boolToProp(Term e) {	
		if (e.getSort() == Bool.sort)
			return Formula.lf.mkFnTerm(Formula.lf.symIsTrue, new Term[] {e});
		else if (e.getSort() == Logic.sort)
			return e;
		else 
			throw new IllegalArgumentException("Bad type when creating BoolProp, " +
					"found: " + e.getSort());
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
		return logicBinaryOp(f1,f2, Formula.lf.symAnd);
	}
	

	// TODO: add comments
	public static Term safe_and(Term f1, Term f2) {
		if (f1.getSort().equals(Bool.sort)) {
			f1 = Logic.boolToProp(f1);
		}
		if (f2.getSort().equals(Bool.sort)) {
			f2 = Logic.boolToProp(f1);
		}
		return and(f1, f2);
	}
	// TODO: add comments
	public static Term safe_implies(Term f1, Term f2) {
		if (f1.getSort().equals(Bool.sort)) {
			f1 = Logic.boolToProp(f1);
		}
		if (f2.getSort().equals(Bool.sort)) {
			f2 = Logic.boolToProp(f1);
		}
		return implies(f1, f2);
	}
	
	/**
	 * Create an object representing an Or.
	 * @param f1 the left parameter of the or
	 * @param f2 the right parameter of the or
	 * @return the newly created object
	 */
	public static Term or(Term f1, Term f2) {
		return logicBinaryOp(f1,f2, Formula.lf.symOr);
	}
	
	
	/**
	 * Creates and returns the negation of a formula
	 * @param f the formula to negate (of type prop)
	 * @return return the new not construct
	 */
	public static Term not(Term f) {
		return logicUnaryOp(f, Formula.lf.symNot);
	}
	
	/**
	 * Create an equals object; it has 2 arguments, and
	 * they must have the same type.
	 * @param l the left argument
	 * @param r the right argument
	 * @return an equal object
	 */
	public static Term equals(Term l, Term r) {
		if(l.getSort() != r.getSort() && 
				(!Num.isNum(r.getSort()) || !Num.isNum(l.getSort())))
			throw new IllegalArgumentException("Different types when creating equals, " +
					"found: " + l.getSort() + " and " + r.getSort());
		FnTerm t = null;
		if(l.getSort() == Bool.sort) {
			t = Formula.lf.mkFnTerm(Formula.lf.symBoolPred, new Term[] {l, r});
			t.tag = NodeBuilder.predEQ;
		}
		if(l.getSort() == Ref.sort) {
			t = Formula.lf.mkFnTerm(Formula.lf.symRefEQ, new Term[] {l, r});
		}
		else if (l.getSort() == Num.sortInt) {
			if(r.getSort() == Num.sortReal) {
				l = Num.intToReal(l);
				t = Formula.lf.mkFnTerm(Formula.lf.symRealPred, new Term[] {l, r});
				t.tag = NodeBuilder.predEQ;
			}
			else {
				t = Formula.lf.mkFnTerm(Formula.lf.symIntPred, new Term[] {l, r});
				t.tag = NodeBuilder.predEQ;
			}
		}
		else if (l.getSort() == Num.sortReal) {
			if(r.getSort() == Num.sortInt) {
				r = Num.intToReal(r);
			}
			t = Formula.lf.mkFnTerm(Formula.lf.symRealPred, new Term[] {l, r});
			t.tag = NodeBuilder.predEQ;
		}
		else {
			t = Formula.lf.mkFnTerm(Formula.lf.symAnyEQ, new Term[]{l, r});
		}
		return  t;
	}
	
	/**
	 * Create an object representing a logical implies.
	 * @param f1 the first element of the implies
	 * @param f2 the second element of the implies
	 * @return a nicely created implies
	 */
	public static Term implies(Term f1, Term f2) {
		return logicBinaryOp(f1,f2, Formula.lf.symImplies);
	}
	
	/**
	 * Create an object representing a logical full implies.
	 * @param f1 the first element of the full implies
	 * @param f2 the second element of the full implies
	 * @return a nicely created fullimplies
	 */
	public static Term fullImplies(Term f1, Term f2) {
		return logicBinaryOp(f1,f2, Formula.lf.symIff);
	} 
	
	/**
	 * Creates a universal binding for only one variable from the formula f.
	 * @param v the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static QuantTerm forall(QuantVariable v, Term f) {
	
		if(f.getSort() != sort)
			throw new IllegalArgumentException("Bad type when creating forall, " +
				"found: " + f.getSort());
		
		return Formula.lf.mkQuantTerm(true, new QuantVariable [] {v}, f, null, null);
	}
	
	/**
	 * Creates a universal binding for only one variable from the formula f.
	 * @param v a reference to the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static QuantTerm forall(QuantVariableRef v, Term f) {
	
		if(f.getSort() != sort)
			throw new IllegalArgumentException("Bad type when creating forall, " +
				"found: " + f.getSort());
		
		return Formula.lf.mkQuantTerm(true, new QuantVariable [] {v.qvar}, f, null, null);
	}
	
	/**
	 * Creates a universal binding for several vars from the formula f.
	 * @param v the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static QuantTerm forall(QuantVariable[] v, Term f) {
	
		if(f.getSort() != sort)
			throw new IllegalArgumentException("Bad type when creating forall, " +
				"found: " + f.getSort());
		
		return Formula.lf.mkQuantTerm(true, v, f, null, null);
	}		
	
	/**
	 * Creates a existential binding for only one variable from the formula f.
	 * @param v the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static QuantTerm exists(QuantVariable v, Term f) {
	
		if(f.getSort() != sort)
			throw new IllegalArgumentException("Bad type when creating exists, " +
				"found: " + f.getSort());
		
		return Formula.lf.mkQuantTerm(false, new QuantVariable [] {v}, f, null, null);
	}

	/**
	 * Creates a existential binding for several vars from the formula f.
	 * @param v the variable to bind
	 * @param f the formula which is the body of the forall
	 * @return the forall construct newly created
	 */
	public static QuantTerm exists(QuantVariable[] v, Term f) {
	
		if(f.getSort() != sort)
			throw new IllegalArgumentException("Bad type when creating exists, " +
				"found: " + f.getSort());
		
		return Formula.lf.mkQuantTerm(false, v, f, null, null);
	}	
	

	
	/**
	 * Returns a boolean le expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
	 */
	public static Term le(Term l, Term r) {
		return numBinaryOp(l,r,NodeBuilder.predLE);
	}

	/**
	 * Returns a boolean lt expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
	 */
	public static Term lt(Term l, Term r) {		
		return numBinaryOp(l,r,NodeBuilder.predLT);
	}

	/**
	 * Returns a boolean ge expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
	 */
	public static Term ge(Term l, Term r) {		
		//return numBinaryOp(l,r,NodeBuilder.predGE);
		return numBinaryOp(r,l,NodeBuilder.predLT);
	}
	
	/**
	 * Returns a boolean gt expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link NodeBuilder#predLE}
	 */
	public static Term gt(Term l, Term r) {		
		//return numBinaryOp(l,r,NodeBuilder.predGT);
		return numBinaryOp(r,l,NodeBuilder.predLE);
	}
	

	/**
	 * Returns a predicate which is the test of the equality to zero
	 * of the specified term.
	 * @param t the term to equal to zero
	 * @return a newly created predicate of the form (t == 0)
	 */
	public static Term equalsZero(Term t) {
		Term res = null;
		if(t.getSort() == Num.sortInt) {
			res = equals(t, Num.value(new Integer(0)));
		}
		else if (t.getSort() == Num.sortReal) {
			res = equals(t, Num.value(new Float(0)));
		}
		else {
			throw new IllegalArgumentException("The sort " + t.getSort() + " is invalid!"); 
		}
		return res;
	}
	
	/**
	 * Returns a predicate that equals the given parameter to 
	 * <code>null</code>. It returns something of the form
	 * <code>t == null</code>.
	 * @param t the parameter to equals to <code>null</code>
	 * @return the predicate that equals <code>t</code> to 
	 * <code>null</code>
	 */
	public static Term equalsNull(Term t) {
		Term res = null;
		if (t.getSort() == Ref.sort) {
			res = equals(t, Ref.Null());
		}
		else {
			throw new IllegalArgumentException("The sort " + t.getSort() + " is invalid!"); 
		}
		return res;
	}

	/**
	 * Builds the term that represents the interval:
	 * <code>0 &le; idx /\ idx &lt; dim</code>. It is
	 * mainly used for array building.
	 * @param dim the max dimension
	 * @param idx the index that is within the interval
	 * @return a term representing an index within an interval
	 */
	public static Term interval0To(Term dim, QuantVariableRef idx) {
		if((!dim.getSort().equals(Num.sortInt)) ||(!idx.getSort().equals(Num.sortInt)))
			throw new IllegalArgumentException("The sort " + dim.getSort() + " or " +
					idx.getSort()+
					" is invalid! (Hint: should be int...)"); 
		return Logic.and(Logic.le(Num.value(0), idx), Logic.lt(idx, dim));
	}
	
	/**
	 * Builds a term that represents a subtype relation
	 * @param t1 the first type
	 * @param t2 the second type to compare
	 * @return a predicate that represents a subtype relation
	 */
	public static FnTerm typeLE(Term t1, Term t2) {
		if(!t1.getSort().equals(Type.sort) || !t2.getSort().equals(Type.sort)) {
			throw new IllegalArgumentException("The given sorts were bad... it should be " +
					"types, found " + t1.getSort() + " and " + t2.getSort());
		}
		return Formula.lf.mkFnTerm(Formula.lf.symTypeLE, new Term[] {t1, t2});
	}
	
	/**
	 * Create the predicate that tells if a value is compatible with a specific type.
	 * @param heap the current heap
	 * @param val the value to check
	 * @param type the type to check
	 * @return the newly formed predicate
	 */
	public static Term assignCompat(Term heap, Term val, Term type) {
		if(heap.getSort() != Heap.sort)
			throw new IllegalArgumentException("Type of the first param should be heap (" + Heap.sort + "), found: " + heap.getSort());
		if(type.getSort() != Type.sort)
			throw new IllegalArgumentException("Type of the second param should be ref (" + Type.sort + "), found: " + type.getSort());

		return Formula.lf.mkFnTerm(Formula.lf.symAssignCompat, new Term [] {heap, val, type});
	}
	
	/**
	 * Main for testing purpose.
	 * @param args ignored
	 */
	public static void main(String [] args) {
		QuantVariable [] vars = { Expression.var("v1", Logic.sort),
								  Expression.var("v2", Bool.sort) };
		
		QuantVariableRef rv1 = Expression.rvar(vars[0]);
		QuantVariableRef rv2 = Expression.rvar(vars[1]);
		Term formula = 
			 Logic.forall(vars, Logic.implies(rv1, rv2));
		System.out.println(formula);
		System.out.println(formula.subst(rv2,
				Logic.implies(Logic.boolToProp(rv2), 
						Logic.False())));
		System.out.println(Logic.and(Logic.True(), Logic.False()));
	}
}
