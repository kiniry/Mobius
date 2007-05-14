/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.NodeBuilder.STerm;

public class CPred extends CTerm implements SPred {
	// TODO: add comments
	public CPred(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	public CPred(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CPred(String rep) {
		super(false, rep, new STerm[0]);
	}
	
	// TODO: add comments
	public CPred(boolean b, String rep, STerm t1, STerm t2) {
		this(b, rep, new STerm [] {t1, t2});
	}
}