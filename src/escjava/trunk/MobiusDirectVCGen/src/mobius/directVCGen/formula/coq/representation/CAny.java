/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SMap;
import escjava.sortedProver.NodeBuilder.STerm;

public class CAny extends CTerm implements SMap {
	// TODO: add comments
	public CAny(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	public CAny(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CAny(String rep) {
		super(false, rep, new STerm[0]);
	}
}