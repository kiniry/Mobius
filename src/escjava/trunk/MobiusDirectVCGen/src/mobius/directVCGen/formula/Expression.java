package mobius.directVCGen.formula;

import javafe.ast.FormalParaDecl;
import javafe.ast.GenericVarDecl;
import javafe.ast.LocalVarDecl;
import escjava.ast.TagConstants;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;
import escjava.translate.UniqName;

public class Expression {
	
	
	public static QuantVariableRef var(String str) {
		QuantVariable v = Formula.lf.mkQuantVariable(str, Logic.sort);
		return Formula.lf.mkQuantVariableRef(v);
	}
	private static int varCounter = 0;

	public static QuantVariableRef var(Sort s) {
		QuantVariable v =  Formula.lf.mkQuantVariable("x" + varCounter++, s);
		return Formula.lf.mkQuantVariableRef(v);
	}
	public static FnTerm sym(String name, Sort s) {
		return Formula.lf.symbolRef (name, s);
	}
	public static QuantVariable var(String name, Sort s) {
		return Formula.lf.mkQuantVariable(name, s);
	}
	
	public static FnTerm typeof(Term heap, Term var) {
		return Formula.lf.mkFnTerm(Formula.lf.symTypeOf, new Term[] {heap, var});
	}
	public static QuantVariableRef refFromVar(QuantVariable qv) {
		return Formula.lf.mkQuantVariableRef(qv);
	}
	public static QuantVariable var(GenericVarDecl decl) {
		return Formula.lf.mkQuantVariable(decl, UniqName.variable(decl));
	}
	public static QuantVariableRef var(FormalParaDecl arg) {
		return refFromVar(Formula.lf.mkQuantVariable(arg, UniqName.variable(arg)));
	}
	public static Term bitor(Term l, Term r) {
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if(l.getSort() == Bool.sort) {
			t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
			t.tag = TagConstants.BITOR;
		}
		else if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
			t.tag = TagConstants.BITOR;
		}
		else if (l.getSort() == Num.sortReal) {
			t = Formula.lf.mkFnTerm(Formula.lf.symRealFn, new Term[] {l, r});
			t.tag = TagConstants.BITOR;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}
	public static Term bitxor(Term l, Term r) {
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if(l.getSort() == Bool.sort) {
			t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
			t.tag = TagConstants.BITXOR;
		}
		else if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
			t.tag = TagConstants.BITXOR;
		}
		else if (l.getSort() == Num.sortReal) {
			t = Formula.lf.mkFnTerm(Formula.lf.symRealFn, new Term[] {l, r});
			t.tag = TagConstants.BITXOR;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}
	public static Term bitand(Term l, Term r) {
		if(l.getSort() != r.getSort())
			throw new IllegalArgumentException("The sort of " + l + 
					" is different from the sort of " + r + ".");
		FnTerm t = null;
		if(l.getSort() == Bool.sort) {
			t = Formula.lf.mkFnTerm(Formula.lf.symBoolFn, new Term[] {l, r});
			t.tag = TagConstants.BITAND;
		}
		else if (l.getSort() == Num.sortInt) {
			t = Formula.lf.mkFnTerm(Formula.lf.symIntFn, new Term[] {l, r});
			t.tag = TagConstants.BITAND;
		}
		else if (l.getSort() == Num.sortReal) {
			t = Formula.lf.mkFnTerm(Formula.lf.symRealFn, new Term[] {l, r});
			t.tag = TagConstants.BITAND;
		}
		else {
			throw new IllegalArgumentException("The sort " + l.getSort() + " is invalid!"); 
		}
		return t;
	}
	
}
