package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SBool;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * This class represents formulas of type bool.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CBool extends CValue implements SBool {
  /**
   * Construct a boolean formula.
   * @param pref true if the symbol is prefix
   * @param rep the symbol attached to this node
   * @param args the children of the node
   */
  public CBool(final boolean pref, final String rep, final STerm [] args) {
    super(pref, rep, args);
  }

  /**
   * Construct a boolean formula, with its symbol as a prefix.
   * @param rep the symbol attached to this node
   * @param args the children of the node
   */
  public CBool(final String rep, final STerm [] args) {
    this(true, rep, args);
  }

  /**
   * Create a node with no child.
   * @param rep the symbol of the node
   */
  public CBool(final String rep) {
    this(false, rep, new STerm[0]);
  }
}
