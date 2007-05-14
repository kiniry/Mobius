/**
 * 
 */
package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SAny;
import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.Sort;

public class CTerm implements STerm, SAny {
	
	// TODO: add comments
	private String rep;
	
	/** tells if the notation is a prefix notation */
	private final boolean prefix;
	
	// TODO: add comments
	protected final STerm [] args;
	
	// TODO: add comments
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
	
	// TODO: add comments
	public boolean isSubSortOf(Sort s) {
		throw new UnsupportedOperationException("This operation is not used it seems...");
	}
}