
package mobius.directVCGen.formula.coq.representation;

import mobius.directVCGen.formula.coq.CoqNodeBuilder;
import escjava.sortedProver.NodeBuilder.QuantVar;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class represents the forall construct.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CForall extends CPred {
  /** a builder to help pretty print. */
  private final CoqNodeBuilder fBuilder;

  /** the array of variables to quantify. */
  public final QuantVar[] fVars;

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
  
  /*
   * (non-Javadoc)
   * @see mobius.directVCGen.formula.coq.CoqNodeBuilder.CTerm#toString()
   */
  public String toString() {
    String res  = "(forall";
    for (QuantVar v: fVars) {
      res += " (" + CoqNodeBuilder.normalize(v.name) + ":" + this.fBuilder.buildSort(v.type) + ")";
    }
    res += ", " + fArgs[0] + ")";
    return res;
  }
}
