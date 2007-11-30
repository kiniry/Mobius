package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SRef;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class is used to represent formulas of type reference.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CRef extends CValue implements SRef {
  /**
   * Constructs a formula of type reference.
   * @param pref if true the symbol is considered as prefix
   * @param rep the symbol attached to the node
   * @param args the children of the node
   */
  public CRef(final boolean pref, final String rep, final STerm [] args) {
    super(pref, rep, args);
  }

  /**
   * Constructs a formula of type reference where its
   * symbol is considered as a prefix.
   * @param rep the symbol attached to this formula
   * @param args the children of the formula
   */
  public CRef(final String rep, final STerm [] args) {
    super(true, rep, args);
  }
  
  /**
   * Constructs a formula of type reference where its
   * symbol is considered as a prefix.
   * @param rep the symbol attached to this formula
   * @param arg the child of the formula
   */
  public CRef(final String rep, final STerm arg) {
    super(true, rep, new STerm [] {arg});
  }
  /**
   * Constructs a formula of type reference with no child.
   * @param rep the symbol attached to this node
   */
  public CRef(final String rep) {
    super(false, rep, new STerm[0]);
  }
}
