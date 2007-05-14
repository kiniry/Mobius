package mobius.directVCGen.formula.coq.representation;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.NodeBuilder.QuantVar;
import escjava.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * The class representing an exists object.
 * @author J. Charles
 */
public class CExists extends CForall {
	/** the builder  which created this object */
	private final CoqNodeBuilder builder;
	

	/**
	 * Build an exists object. 
	 * @param builder the builder which is creating this object.
	 * @param vars the variables to quantify upon
	 * @param body the body of the exists
	 */
	public CExists(CoqNodeBuilder builder, QuantVar[] vars, STerm body) {
		super(builder, new QuantVar[] {vars[0]}, buildExists(builder, vars, (SPred)body, 1));
		this.builder = builder;
	}
	

	/**
	 * A constructor to have just a single variable for 
	 * each exists sign.
	 * @param builder the builder which is creating this object.
	 * @param vars the variables to quantify upon
	 * @param body the body of the exists
	 * @param idx which variable we are currently quantifying in the
	 * object
	 */
	private CExists(CoqNodeBuilder builder, QuantVar[] vars, STerm body, int idx) {
		super(builder, new QuantVar[] {vars[idx]}, 
				buildExists(builder, vars, (SPred)body, idx + 1));
		this.builder = builder;
	}
	
	/**
	 * Build an exist. If <code>idx < vars.length</code>
	 * returns a new exists symbol, else it returns pred.
	 * @param builder the builder which is creating the exists object.
	 * @param vars the variables to quantify upon
	 * @param pred the body of the exists
	 * @param idx which variable we are currently quantifying in the
	 * object
	 * @return a valid term
	 */
	private static STerm buildExists(CoqNodeBuilder builder, QuantVar[] vars, SPred pred, int idx) {
		if (idx == vars.length)
			return pred;
		else {
			return new CExists(builder, vars, pred, idx + 1);
		}
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

}
