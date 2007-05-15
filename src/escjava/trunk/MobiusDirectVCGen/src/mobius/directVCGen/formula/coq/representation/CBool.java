package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SBool;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class represents formulas of type bool
 * @author J. Charles
 */
public class CBool extends CValue implements SBool {
	/**
	 * Construct a boolean formula.
	 * @param pref true if the symbol is prefix
	 * @param rep the symbol attached to this node
	 * @param args the children of the node
	 */
	public CBool(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	/**
	 * Construct a boolean formula, with its symbol as a prefix.
	 * @param rep the symbol attached to this node
	 * @param args the children of the node
	 */
	public CBool(String rep, STerm [] args) {
		this(true, rep, args);
	}
	
	/**
	 * Create a node with no child
	 * @param rep the symbol of the node
	 */
	public CBool(String rep) {
		this(false, rep, new STerm[0]);
	}
}