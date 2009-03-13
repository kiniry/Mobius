
package mobius.directVCGen.formula.coq.representation;

import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.Util;
import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.NodeBuilder.QuantVar;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class represents the forall construct.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CForall extends CPred {
  /** the array of variables to quantify. */
  private final QuantVar[] fVars;
  
  /** a builder to help pretty print. */
  private final CoqNodeBuilder fBuilder;



  /**
   * Constructs a forall.
   * @param builder the builder to pretty print the variables
   * @param vars the variable list
   * @param body the body of the forall
   */
  public CForall(final CoqNodeBuilder builder, final QuantVar[] vars, final STerm body) {
    super(false, "forall", new STerm[]{body});
    this.fBuilder = builder;
    this.fVars = vars;
  }
  

  /**
   * @return a forall understandable by Coq, e.g.:
   * <code>
   * (forall (v1: Type1) (v2: Type2)... body)
   * </code>
   */
  public String toString() {
    String res  = "(forall";
    int i = 0;
    for (QuantVar v: fVars) {
      i++;
      i %= 4;
      if (i == 0) {
        res += "\n    "; 
      }
      
      // every 4 variables it goes down the line
      if (v.type.equals(Ref.sort)) {
        
        // Location$
        res += " (" + Util.normalize(v.name) + ": Location)";
      }
      else {
        res += " (" + Util.normalize(v.name) + ":" + 
                 this.fBuilder.buildSort(v.type) + ")";
      }
      

    }
    res += ",\n  " + getArgs()[0] + ")";
    return res;
  }


  public QuantVar[] getVars() {
    return fVars;
  }
}
