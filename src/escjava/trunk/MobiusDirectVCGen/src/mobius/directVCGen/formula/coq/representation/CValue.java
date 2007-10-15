package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SInt;
import escjava.sortedProver.NodeBuilder.SRef;
import escjava.sortedProver.NodeBuilder.STerm;
import escjava.sortedProver.NodeBuilder.SValue;

/**
 * This class represents formulas of type value.
 * They should not be used much, to be true, it is mainly used
 * for select and store relations. Otherwise all data formulas
 * (<i>eg.</i> Ref, Int, <i>etc.</i>...) subclass this class.
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CValue extends CAny implements SValue, SRef, SInt {
  /**
   * Constructs a formula of type value.
   * @param pref if true the symbol is considered as a prefix
   * @param rep the symbol attached to this node
   * @param args the children of the node
   */
  public CValue(final boolean pref, final String rep, final STerm [] args) {
    super(pref, rep, args);
  }

  /**
   * Constructs a formula of type value, with its symbol considered as a prefix.
   * @param rep the symbol attached to the node
   * @param args the children of the node
   */
  public CValue(final String rep, final STerm [] args) {
    super(true, rep, args);
  }

  /**
   * Constructs a formula of type value; but with no child.
   * @param rep the symbol attached to this node
   */
  public CValue(final String rep) {
    super(false, rep, new STerm[0]);
  }

  /**
   * Constructs a formula of type value which has only one child.
   * @param rep the symbol attached to this node
   * @param t the child attached to this node
   */
  public CValue(final String rep, final CTerm t) {
    this(rep, new STerm[]{t});
  }
}
