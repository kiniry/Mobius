
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SInt;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * A class to represent integers formulas.
 * @author J. Charles
 */
public class CInt extends CValue implements SInt {
	/**
	 * Construct an integer formula.
	 * @param pref if true the symbol must be shown as a prefix
	 * @param rep the symbol attached to this node
	 * @param args the children of the node
	 */
	public CInt(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	/**
	 * Construct an integer formula, and the given symbol is considered as
	 * prefix.
	 * @param rep the symbol attached to this node
	 * @param args the children of the node
	 */
	public CInt(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	/**
	 * Construct an integer formula which is only the given symbol.
	 * @param rep the symbol of the formula
	 */
	public CInt(String rep) {
		super(false, rep, new STerm[0]);
	}
	
	/**
	 * Construct an integer formula which contain only one child.
	 * @param rep the symbol associated with the formula
	 * @param arg the child associated with the formula
	 */
	public CInt(String rep, STerm arg) {
		this(rep, new STerm[] {arg});
	}
}