package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SAny;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class is used to represent terms of type any.
 * Should not be used, outside subclassing.
 * 
 * @author J. Charles
 */
class CAny extends CTerm implements SAny {
	// TODO: add comments
	protected CAny(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	protected CAny(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	protected CAny(String rep) {
		super(false, rep, new STerm[0]);
	}
}