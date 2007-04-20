package mobius.directVCGen.formula;

import escjava.ast.TagConstants;
import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

public class Bool {
	/** the sort representing the booleans */
	public static Sort sort = Formula.lf.sortBool;
		
	/**
	 * Returns the term representing the given value b.
	 * @param b The boolean value to convert to a term
	 * @return a BoolLiteral term
	 */
	public static Term value(Boolean b) {	
		return Formula.lf.mkBoolLiteral(b);
	}

	/**
	 * Returns the right equality from the argument type.
	 * @param l The left element of the equality
	 * @param r The right element of the equality
	 * @return an equality over the terms
	 * @throws IllegalArgumentException if the types of the arguments are bad.
	 */
	public static Term equals(Term l, Term r) {
		if(l.getSort() != r.getSort() && 
				(!Num.isNum(r.getSort()) || !Num.isNum(l.getSort())))
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if(l.getSort() == Bool.sort) {
			t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
		}
		else if (l.getSort() == Num.sortReal) {
			if(r.getSort() == Num.sortInt) {
				r = Num.intToReal(r);
			}
			t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
		}
		else if (l.getSort() == Num.sortInt) {
			if(r.getSort() == Num.sortReal) {
				l = Num.intToReal(l);
				t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
			}
			else {
				t = Formula.lf.mkFnTerm(Formula.lf.symIntBoolFn, new Term[] {l, r});
			}
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		t.tag = NodeBuilder.predEQ;
		return t;
	}

	/**
	 * Returns a boolean Or expression.
	 * @param l The left element of the expression
	 * @param r The right element of the expression
	 * @return a term representing a boolean or 
	 * a FnTerm with tag {@link TagConstants#BOOLOR}
	 */
	public static Term or(Term l, Term r) {
		if(l.getSort() != Bool.sort || r.getSort() != Bool.sort)
			throw new IllegalArgumentException("The sorts of the arguments should be bool found: " + l.getSort() + 
					" and " + r + ".");
		FnTerm t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
		t.tag = TagConstants.BOOLOR;
		return t;
	}
	 
	/**
	 * Returns a boolean and expression.
	 * @param l The left element of the expression
	 * @param r The right expression of the expression
	 * @return The and expression a FnTerm with tag {@link TagConstants#BOOLAND}
	 */
	public static Term and(Term l, Term r) {
		if(l.getSort() != Bool.sort || r.getSort() != Bool.sort)
			throw new IllegalArgumentException("The sorts of the arguments should be bool found: " + l.getSort() + 
					" and " + r + ".");
		FnTerm t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
		t.tag = TagConstants.BOOLAND;
		return t;
	}

	/**
	 * Returns a boolean not expression.
	 * @param t the boolean expression to turn to a not
	 * @return A Not expression of type FnTerm with tag {@link TagConstants#BOOLNOT}
	 */
	public static Term not(Term t) {
		if(t.getSort() != Bool.sort )
			throw new IllegalArgumentException("The sorts of the arguments should be bool found: " + t.getSort());
		FnTerm res = Formula.lf.mkFnTerm(Formula.lf.symBoolUnaryFn, new Term[] {t});
		res.tag = TagConstants.BOOLNOT;
		return res;
	}


	public static Term le(Term l, Term r) {
		if(l.getSort() != r.getSort() &&
				(!Num.isNum(l.getSort()) || !Num.isNum(r.getSort())))
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			if(r.getSort() == Num.sortReal) {
				l = Num.intToReal(l);
				t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
			}
			else {
				t = Formula.lf.mkFnTerm(Formula.lf.symIntBoolFn, new Term[] {l, r});
			}
			
		}
		else if (l.getSort() == Num.sortReal) {
			if(r.getSort() == Num.sortInt) {
				r = Num.intToReal(r);
			}
			t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		t.tag = NodeBuilder.predLE;
		return t;
	}

	public static Term lt(Term l, Term r) {		
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			if(r.getSort() == Num.sortReal) {
				l = Num.intToReal(l);
				t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
			}
			else {
				t = Formula.lf.mkFnTerm(Formula.lf.symIntBoolFn, new Term[] {l, r});
			}
		}
		else if (l.getSort() == Num.sortReal) {
			if(r.getSort() == Num.sortInt) {
				r = Num.intToReal(r);
			}
			t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		t.tag = NodeBuilder.predLT;
		return t;
	}
}
