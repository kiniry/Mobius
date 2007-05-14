package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.QuantVariableRef;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

// TODO: add comments
public class Ref {
	/** the sort that represents references */
	public static Sort sort = Formula.lf.sortRef;

	// TODO: add comments
	public static QuantVariableRef varThis = Expression.rvar(Expression.var("this", Ref.sort));
	
	// TODO: add comments
	public static Term Null() {
		return Formula.lf.mkNullLiteral();
	}

	// TODO: add comments
	public static Term strValue(String string) {
		return Formula.lf.symbolRef(string);
	}


}
