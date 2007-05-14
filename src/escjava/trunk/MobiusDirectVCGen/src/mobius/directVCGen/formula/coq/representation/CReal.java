/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SReal;
import escjava.sortedProver.NodeBuilder.STerm;

public class CReal extends CValue implements SReal {
	// TODO: add comments
	public CReal(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	public CReal(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CReal(String rep) {
		super(false, rep, new STerm[0]);
	}
}