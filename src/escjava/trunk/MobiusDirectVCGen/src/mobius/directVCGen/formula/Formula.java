package mobius.directVCGen.formula;

import javafe.ast.Type;
import javafe.ast.VarInit;
import javafe.tc.FlowInsensitiveChecks;
import escjava.sortedProver.Lifter;
import escjava.sortedProver.Lifter.Term;
import escjava.sortedProver.NodeBuilder.Sort;

public class Formula {
	static Lifter lf = new Lifter(null);
	
	public static Lifter getCurrentLifter() {
		return lf;
	}

	public static Term translate(Type type) {
		return lf.symbolRef(type.toString());
	}
	public static Sort getSort(VarInit e) {
		Type t = FlowInsensitiveChecks.getType(e);
		return lf.typeToSort(t);
	}
}
