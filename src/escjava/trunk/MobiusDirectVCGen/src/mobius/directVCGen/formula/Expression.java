package mobius.directVCGen.formula;

import javafe.ast.FormalParaDecl;
import javafe.ast.LocalVarDecl;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.QuantVariable;
import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;
import escjava.translate.UniqName;

public class Expression {
	public static QuantVariableRef preHeap = refFromVar(var("\\preHeap", Formula.sort));
	public static QuantVariableRef heap = refFromVar(var("\\heap", Formula.sort));
	public static QuantVariableRef varthis = refFromVar(var("this", Ref.sort));
	
	
	public static QuantVariableRef var(String str) {
		QuantVariable v = null;
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
	public static QuantVariable var(LocalVarDecl decl) {
		return Formula.lf.mkQuantVariable(decl, UniqName.variable(decl));
	}
	public static QuantVariableRef var(FormalParaDecl arg) {
		return refFromVar(Formula.lf.mkQuantVariable(arg, UniqName.variable(arg)));
	}
	
}
