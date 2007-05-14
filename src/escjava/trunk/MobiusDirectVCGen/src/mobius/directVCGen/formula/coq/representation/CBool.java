/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SBool;
import escjava.sortedProver.NodeBuilder.STerm;

public class CBool extends CValue implements SBool {
	// TODO: add comments
	public CBool(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	public CBool(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CBool(String rep) {
		super(false, rep, new STerm[0]);
	}
}