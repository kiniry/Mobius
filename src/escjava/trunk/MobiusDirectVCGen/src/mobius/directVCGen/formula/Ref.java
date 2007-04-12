package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.Term;

public class Ref {

	public static Term Null() {
		return Formula.lf.mkNullLiteral();
	}

	public static Term strValue(String string) {
		return Formula.lf.symbolRef(string);
	}

}
