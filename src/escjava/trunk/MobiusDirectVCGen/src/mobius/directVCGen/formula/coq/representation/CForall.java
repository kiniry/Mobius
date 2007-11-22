
package mobius.directVCGen.formula.coq.representation;

import mobius.directVCGen.formula.Ref;
import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.NodeBuilder.QuantVar;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class represents the forall construct.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CForall extends CPred {
  /** the array of variables to quantify. */
  final QuantVar[] fVars;
  
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
    for (QuantVar v: fVars) {
      // local var memory is not used anymore
//      if (v.name.startsWith("lv") && v.name.length() <= 3) {
//        res += " (" + CoqNodeBuilder.normalize(v.name) + ": LocalVar.t)";
//      }
//      else 
      if (v.type.equals(Ref.sort)) {
        // Location$
        res += " (" + CoqNodeBuilder.normalize(v.name) + ": Location)";
      }
      else {
        res += " (" + CoqNodeBuilder.normalize(v.name) + ":" + 
                 this.fBuilder.buildSort(v.type) + ")";
      }
    }
    res += ", " + fArgs[0] + ")";
    return res;
  }
}
