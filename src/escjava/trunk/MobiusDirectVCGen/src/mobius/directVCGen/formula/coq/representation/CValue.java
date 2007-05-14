/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.SValue;

public class CValue extends CAny implements SValue {
	// TODO: add comments
	public CValue(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	public CValue(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CValue(String rep) {
		super(false, rep, new STerm[0]);
	}
	
	// TODO: add comments
	public CValue(String rep, CTerm t) {
		this(rep, new STerm[]{t});
	}
}