package mobius.directVCGen.formula;

import escjava.sortedProver.NodeBuilder;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

public class Num {
	/** the sort that represents integers */
	public static Sort sortInt = Formula.lf.sortInt;
	/** the sort that represents real numbers */
	public static Sort sortReal = Formula.lf.sortReal;

	public static Term value(Long l) {	
		return Formula.lf.mkIntLiteral(l);
	}

	public static Term value(Integer i) {
		return Formula.lf.mkIntLiteral(i.longValue());
	}

	public static Term value(Byte b) {
		return Formula.lf.mkIntLiteral(b.longValue());
	}
	public static Term value(Short s) {
		return Formula.lf.mkIntLiteral(s.longValue());
	}
	public static Term value(Float f) {
		return Formula.lf.mkRealLiteral(f.doubleValue());
	}

	public static Term value(Character c) {
		return Formula.lf.mkIntLiteral(c.charValue());
	}

	public static Term value(Double d) {		
		return Formula.lf.mkRealLiteral(d);
	}

	private static Term arith(Term l, Term r, int tag) {
		if(l.getSort() != r.getSort()&& 
				(!Num.isNum(r.getSort()) || !Num.isNum(l.getSort())))
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if(l.getSort() != r.getSort()) {
			if(l.getSort() == Num.sortInt) {
				l = Num.intToReal(l);
			}
			else {
				r = Num.intToReal(r);
			}
		}
		if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
			t.tag = tag;
		}
		else if (l.getSort() == Num.sortReal) {
			t = Formula.lf.mkFnTerm(Formula.lf.symRealFn, new Term[] {l, r});
			t.tag = tag;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}
	public static Term add(Term l, Term r) {
		return arith(l, r, NodeBuilder.funADD);
	}
	
	
	public static Term sub(Term l, Term r) {
		return arith(l, r, NodeBuilder.funSUB);
	
	}
	
	public static Term div(Term l, Term r) {
		return arith(l, r, NodeBuilder.funDIV);
	}
	
	public static Term mul(Term l, Term r) {
		return arith(l, r, NodeBuilder.funMUL);
	}
	
	public static Term mod(Term l, Term r) {
		return arith(l, r, NodeBuilder.funMOD);
	}

	
	public static Term lshift(Term l, Term r) {
		// TODO: understand when to handle 64 bits case
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
			t.tag = NodeBuilder.funSL32;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}

	public static Term rshift(Term l, Term r) {
		// TODO: understand when to handle 64 bits case
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
			t.tag =  NodeBuilder.funASR32;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}

	public static Term urshift(Term l, Term r) {
		// TODO: understand when to handle 64 bits case
		if(l.getSort() != r.getSort()&& 
				(!Num.isNum(r.getSort()) || !Num.isNum(l.getSort())))
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
			t.tag = NodeBuilder.funUSR32;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}

	public static boolean isNum(Sort sort) {
		return sort == sortInt || sort == sortReal;
	}

	public static Term intToReal(Term r) {
		return Formula.lf.mkFnTerm(Formula.lf.symIntToReal, new Term [] {r});
	}
}
