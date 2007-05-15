
package mobius.directVCGen.formula.coq.representation;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.NodeBuilder.QuantVar;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class represents the forall construct.
 * @author J. Charles
 */
public class CForall extends CPred {
	/** a builder to help pretty print*/
	private final CoqNodeBuilder builder;

	/** the array of variables to quantify */
	public final QuantVar[] vars;

	/**
	 * Constructs a forall.
	 * @param builder the builder to pretty print the variables
	 * @param vars the variable list
	 * @param body the body of the forall
	 */
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