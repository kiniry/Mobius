package mobius.directVCGen.formula;

import javafe.ast.Expr;
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
	
	public static Sort typeToSort(javafe.ast.Type t) {
		return Formula.lf.typeToSort(t);
	}
	public static boolean isSubClassOrEq(Term typ1, Term typ2) {
		// TODO Auto-generated method stub
		return false;
	}
	public static Term getType(VarInit expr) {
		return translate(FlowInsensitiveChecks.getType(expr)) ;
	}
	public static Term javaLangThrowable() {
		// TODO Auto-generated method stub
		return null;
	}
	/**
	 * @deprecated used for convenience only
	 */
	public static Term getJavaLang(String string) {
		// TODO Auto-generated method stub
		return null;
	}
	public static Term javaLangArithmeticException() {
		// TODO Auto-generated method stub
		return null;
	}
	public static Term javaLangNullPointerException() {
		// TODO Auto-generated method stub
		return null;
	}
}
