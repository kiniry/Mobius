package mobius.directVCGen.formula;

import escjava.sortedProver.Lifter.Term;

public class Num {

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
