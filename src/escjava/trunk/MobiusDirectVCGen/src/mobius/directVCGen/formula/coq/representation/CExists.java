package mobius.directVCGen.formula.coq.representation;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.NodeBuilder.QuantVar;
import escjava.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.NodeBuilder.STerm;

// TODO: add comments
public class CExists extends CForall {
	private CoqNodeBuilder builder;
	// TODO: add comments
	public CExists(CoqNodeBuilder builder, QuantVar[] vars, STerm body) {
		super(builder, new QuantVar[] {vars[0]}, builder.buildExists(removeFirst(vars), (SPred)body));
		this.builder = builder;
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.coq.CoqNodeBuilder.CForall#toString()
	 */
	public String toString() {
		String res  = "(exists";
		res +=  CoqNodeBuilder.normalize(vars[0].name) + ":" + builder.buildSort(vars[0].type);
		res += ", " + args[0] + ")";
		return res;
	}
	//TODO: add comments
	public static QuantVar[] removeFirst(QuantVar[] vars) {
		QuantVar[] res = new QuantVar [vars.length - 1];
		for(int i = 1; i < vars.length; i++) {
			res[i -1] = vars[i];
		}
		return res;
	}
}
