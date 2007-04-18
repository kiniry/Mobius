package mobius.directVCGen.formula;

import javafe.ast.VarInit;
import javafe.tc.FlowInsensitiveChecks;
import escjava.sortedProver.Lifter.FnTerm;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

public class Type {
	public static Sort sort = Formula.lf.sortType;
	public static FnTerm of(Term heap, Term var) {
		return Formula.lf.mkFnTerm(Formula.lf.symTypeOf, new Term[] {heap, var});
	}
	public static Term translate(javafe.ast.Type type) {
		return Formula.lf.symbolRef(type.toString());
	}
	
	public static Sort getSort(VarInit e) {
		javafe.ast.Type t = FlowInsensitiveChecks.getType(e);
		return Formula.lf.typeToSort(t);
	}
	
	/**
	 * @deprecated
	 */
	public static javafe.ast.Type getType(VarInit e) {
		javafe.ast.Type t = FlowInsensitiveChecks.getType(e);
		return t;
	}
	public static Sort typeToSort(javafe.ast.Type t) {
		return Formula.lf.typeToSort(t);
	}
}
