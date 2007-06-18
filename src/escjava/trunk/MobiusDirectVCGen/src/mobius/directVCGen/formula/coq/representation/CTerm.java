package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.Sort;

/**
 * This class is used to represent terms.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CTerm implements STerm {

  /** the array containing all the children of the term. */
  protected final STerm [] fArgs;
  
  /** the symbol or name associated with the node. */
  private final String fRep;

  /** tells if the notation is a fPrefix notation. */
  private final boolean fPrefix;
  



  /**
   * 
   * @param prefix if the symbol of the term should be a fPrefix
   * or not
   * @param rep the symbol of the term
   * @param args the children of the term
   */
  public CTerm (final boolean prefix, final String rep, final STerm [] args) {
    this.fPrefix = prefix;
    this.fRep = rep;
    this.fArgs = args;
  }

  /*
   * (non-Javadoc)
   * @see java.lang.Object#toString()
   */
  public String toString() {
    String res = "";
    if (fArgs.length == 0) {
      return fRep;
    } 
    else if (fArgs.length == 1) {
      if (fPrefix) {
        res = "(" + fRep + " " + fArgs[0] + ")";
      }
      else {
        res = "(" + fArgs[0] + " " + fRep + ")";
      }
    }
    else {
      if ((!fPrefix) && (fArgs.length == 2)) {
        
        res = "(" + fArgs[0] + " " + fRep + " " + fArgs[1] + ")";
      }
      else {
        res = "(" + fRep;
        for (STerm t: fArgs) {
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
   * @param s ignored
   * @return will not happen
   * @throws  UnsupportedOperationException
   */
  public boolean isSubSortOf(final Sort s) {
    throw new UnsupportedOperationException("This operation is not used it seems...");
  }
}
