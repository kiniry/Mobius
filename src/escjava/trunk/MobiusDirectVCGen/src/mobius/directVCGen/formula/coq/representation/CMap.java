package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SMap;
import escjava.sortedProver.NodeBuilder.STerm;
/**
 * The class to represent map formulas; the type of the heap.
 * @author J. Charles
 */
public class CMap extends CAny implements SMap {
	/**
	 * Construct a map formula.
	 * @param pref if true the symbol attached to this node is 
	 * considered as a prefix
	 * @param rep the symbol attached to this node
	 * @param args the children of the node
	 */
	public CMap(boolean pref, String rep, STerm [] args) {
		super(pref, rep, args);
	}
	
	/**
	 * Construct a map formula, where its symbol is a prefix.
	 * @param rep the symbol attached to this formula
	 * @param args the children of the formula
	 */
	public CMap(String rep, STerm [] args) {
		super(true, rep, args);
	}
	
	/**
	 * Construct a map formula containing only a symbol
	 * and no child.
	 * @param rep the symbol attached to this formula
	 */
	public CMap(String rep) {
		super(false, rep, new STerm[0]);
	}
}