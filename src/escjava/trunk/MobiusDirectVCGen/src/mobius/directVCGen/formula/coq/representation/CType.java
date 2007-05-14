/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SAny;
import escjava.sortedProver.NodeBuilder.STerm;

public class CType extends CTerm implements SAny {
	// TODO: add comments
	public CType(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	public CType(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CType(String rep) {
		super(false, rep, new STerm[0]);
	}
	
	// TODO: add comments
	public CType(String rep, STerm h, STerm loc) {
		this(rep, new STerm[] {h, loc});
	}
}