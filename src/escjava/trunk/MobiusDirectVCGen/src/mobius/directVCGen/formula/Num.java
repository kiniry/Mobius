package mobius.directVCGen.formula;

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

}
