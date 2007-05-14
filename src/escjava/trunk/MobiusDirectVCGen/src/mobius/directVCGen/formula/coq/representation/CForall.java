/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.NodeBuilder.QuantVar;
import escjava.sortedProver.NodeBuilder.STerm;

public class CForall extends CPred {
	/**
	 * 
	 */
	private final CoqNodeBuilder builder;
	// TODO: add comments
	public final QuantVar[] vars;
	// TODO: add comments
	public CForall(CoqNodeBuilder builder, QuantVar[] vars, STerm body) {
		super(false, "forall", new STerm[]{body});
		this.builder = builder;
		this.vars = vars;
	}
	
	/*
	 * (non-Javadoc)
	 * @see mobius.directVCGen.formula.coq.CoqNodeBuilder.CTerm#toString()
	 */
	public String toString() {
		String res  = "(forall";
		for(QuantVar v: vars) {
			res += " (" + CoqNodeBuilder.normalize(v.name) + ":" + this.builder.buildSort(v.type) + ")";
		}
		res += ", " + args[0] + ")";
		return res;
	}

}