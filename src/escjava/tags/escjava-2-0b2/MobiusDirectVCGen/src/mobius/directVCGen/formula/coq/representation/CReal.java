package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SReal;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class is made to represent formulas of real elements.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CReal extends CValue implements SReal {
  /**
   * Constructs a formula of type real.
   * @param pref if true the symbol is considered as prefix
   * @param rep the symbol attached to this node
   * @param args the children of the node
   */
  public CReal(final boolean pref, final String rep, final STerm [] args) {
    super(pref, rep, args);
  }

  /**
   * Constructs a formula of type real, where its symbol is considered as a prefix.
   * @param rep the symbol attached to this node
   * @param args the children of the node
   */
  public CReal(final String rep, final STerm [] args) {
    super(true, rep, args);
  }

  /**
   * Constructs a formula of type real with
   * no children attached to it.
   * @param rep the symbol attached to the formula
   */
  public CReal(final String rep) {
    super(false, rep, new STerm[0]);
  }
}
