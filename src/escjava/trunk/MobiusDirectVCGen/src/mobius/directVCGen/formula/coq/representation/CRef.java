/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SRef;
import escjava.sortedProver.NodeBuilder.STerm;

public class CRef extends CValue implements SRef {
	// TODO: add comments
	public CRef(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	public CRef(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CRef(String rep) {
		super(false, rep, new STerm[0]);
	}
}