/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SInt;
import escjava.sortedProver.NodeBuilder.STerm;

public class CInt extends CValue implements SInt {
	// TODO: add comments
	public CInt(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	// TODO: add comments
	public CInt(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	// TODO: add comments
	public CInt(String rep) {
		super(false, rep, new STerm[0]);
	}
	
	// TODO: add comments
	public CInt(String rep, STerm arg) {
		this(rep, new STerm[] {arg});
	}
}