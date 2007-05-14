/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SMap;
import escjava.sortedProver.NodeBuilder.STerm;

public class CMap extends CTerm implements SMap {
	// TODO: add comments
	public CMap(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	// TODO: add comments
	public CMap(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CMap(String rep) {
		super(false, rep, new STerm[0]);
	}
}