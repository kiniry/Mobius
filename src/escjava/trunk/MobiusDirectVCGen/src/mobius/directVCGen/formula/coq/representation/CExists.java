package mobius.directVCGen.formula.coq.representation;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.NodeBuilder.QuantVar;
import escjava.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.NodeBuilder.STerm;

// TODO: add comments
public class CExists extends CForall {
	// TODO: add comments
	private CoqNodeBuilder builder;
	
	// TODO: add comments
	public CExists(CoqNodeBuilder builder, QuantVar[] vars, STerm body) {
		super(builder, new QuantVar[] {vars[0]}, buildExists(builder, vars, (SPred)body, 1));
		this.builder = builder;
	}
	
	// TODO: add comments
	private CExists(CoqNodeBuilder builder, QuantVar[] vars, STerm body, int idx) {
		super(builder, new QuantVar[] {vars[idx]}, 
				buildExists(builder, vars, (SPred)body, idx + 1));
		this.builder = builder;
	}
	
	// TODO: add comments
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
