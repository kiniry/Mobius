
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * This class is used to represent terms.
 * @author J. Charles
 */
public class CTerm implements STerm {
	
	/** the symbol or name associated with the node */
	private final String rep;
	
	/** tells if the notation is a prefix notation */
	private final boolean prefix;
	
	/** the array containing all the children of the term */
	protected final STerm [] args;
	

	/**
	 * 
	 * @param prefix if the symbol of the term should be a prefix
	 * or not
	 * @param rep the symbol of the term
	 * @param args the children of the term
	 */
	public CTerm (boolean prefix, String rep, STerm [] args) {
		this.prefix = prefix;
		this.rep = rep;
		this.args = args;
	}
	
	/*
	 * (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString() {
		String res = "";
		if (args.length == 0) {
			return rep;
		} 
		else if(args.length == 1) {
			if(prefix) {
				res = "(" + rep + " " + args[0] + ")";
			}
			else {
				res = "(" + args[0] + " " + rep + ")";
			}
		}
		else {
			if ((!prefix) && (args.length == 2)) {
				
					res = "(" + args[0] + " " + rep + " " + args[1] + ")";
			}
			else {
				res = "(" + rep;
				for (STerm t: args) {
					res += " " + t;
				}
				res += ")";
			}
		}
		return res;
	}
	
	/**
	 * This operation is unsupported. 
	 * It makes no sense to have it.
	 * @throws  UnsupportedOperationException
	 */
	public boolean isSubSortOf(Sort s) {
		throw new UnsupportedOperationException("This operation is not used it seems...");
	}
}