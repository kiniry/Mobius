package mobius.directVCGen.formula;

import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

public class Bool {

	public static Term value(Boolean b) {	
		return Formula.lf.mkBoolLiteral(b);
	}

	public static Term equals(Term l, Term r) {
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if(l.getSort() == Bool.sort) {
			t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
			t.tag = TagConstants.BOOLEQ;
		}
		else if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntBoolFn, new Term[] {l, r});
			t.tag = TagConstants.INTEGRALEQ;
		}
		else if (l.getSort() == Num.sortReal) {
			t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
			t.tag = TagConstants.FLOATINGEQ;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}


	public static Sort sort = Formula.lf.sortBool;


	public static Term or(Term l, Term r) {
		if(l.getSort() != Bool.sort || r.getSort() != Bool.sort)
			throw new IllegalArgumentException("The sorts of the arguments should be bool found: " + l.getSort() + 
					" and " + r + ".");
		FnTerm t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
		t.tag = TagConstants.BOOLOR;
		return t;
	}
	
	public static Term and(Term l, Term r) {
		if(l.getSort() != Bool.sort || r.getSort() != Bool.sort)
			throw new IllegalArgumentException("The sorts of the arguments should be bool found: " + l.getSort() + 
					" and " + r + ".");
		FnTerm t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
		t.tag = TagConstants.BOOLAND;
		return t;
	}

	public static Term not(Term t) {
		if(t.getSort() != Bool.sort )
			throw new IllegalArgumentException("The sorts of the arguments should be bool found: " + t.getSort());
		FnTerm res = Formula.lf.mkFnTerm(Formula.lf.symBoolUnaryFn, new Term[] {t});
		res.tag = TagConstants.BOOLNOT;
		return res;
	}

	public static Term ge(Term l, Term r) {
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntBoolFn, new Term[] {l, r});
			t.tag = TagConstants.INTEGRALGE;
		}
		else if (l.getSort() == Num.sortReal) {
			t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
			t.tag = TagConstants.FLOATINGGE;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}

	public static Term gt(Term l, Term r) {
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntBoolFn, new Term[] {l, r});
			t.tag = TagConstants.INTEGRALGT;
		}
		else if (l.getSort() == Num.sortReal) {
			t = Formula.lf.mkFnTerm(Formula.lf.symRealBoolFn, new Term[] {l, r});
			t.tag = TagConstants.FLOATINGGT;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}
}
