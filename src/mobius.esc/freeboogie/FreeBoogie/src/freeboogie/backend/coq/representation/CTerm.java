package freeboogie.backend.coq.representation;

import java.util.Set;

import freeboogie.backend.Sort;
import freeboogie.backend.Term;


/**
 * This class is used to represent terms.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CTerm extends Term<CTerm> {

  /** the array containing all the children of the term. */
  final CTerm [] fArgs;
  
  /** the symbol or name associated with the node. */
  private final String fRep;

  /** tells if the notation is a fPrefix notation. */
  private final boolean fPrefix;
  



  /**
   * Constructs a COQ term.
   * @param s sort of the term
   * @param prefix if the symbol of the term should be a fPrefix
   * or not
   * @param rep the symbol of the term
   * @param args the children of the term
   */
  public CTerm (Sort s, final boolean prefix, final String rep, final CTerm [] args) {
    super(s);
    fPrefix = prefix;
    fRep = rep;
    fArgs = args;
  }

  /**
   * A well parenthized version of the Coq expression.
   * @return the pretty printed version of the term. 
   */
  public String toString() {
    String res = "";
    if (fArgs.length == 0) {
      return fRep;
    } else if (fArgs.length == 1) {
      if (fPrefix) {
        res = "(" + fRep + " " + fArgs[0] + ")";
      } else {
        res = "(" + fArgs[0] + " " + fRep + ")";
      }
    } else {
      if ((!fPrefix) && (fArgs.length == 2)) {
        
        res = "(" + fArgs[0] + " " + fRep + " " + fArgs[1] + ")";
      } else {
        res = "(" + fRep;
        for (CTerm t: fArgs) {
          res += " " + t;
        }
        res += ")";
      }
    }
    return res;
  }

  @Override
  public void addAxiom(CTerm newAxiom) {
      // TODO Auto-generated method stub
  }

  @Override
  public void collectAxioms(Set<CTerm> axiomBag) {
      // TODO Auto-generated method stub
  }
}
