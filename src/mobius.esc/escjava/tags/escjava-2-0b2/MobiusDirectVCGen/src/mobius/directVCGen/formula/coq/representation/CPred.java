package mobius.directVCGen.formula.coq.representation;

import escjava.sortedProver.NodeBuilder.SPred;
import escjava.sortedProver.NodeBuilder.STerm;

/**
 * A class to represent formulas of type predicate (prop in Coq terms).
 * @author J. Charles (julien.charles@inria.fr)
 */
public class CPred extends CTerm implements SPred {
  /**
   * Constructs a formula of type pred.
   * @param pref if the symbol is prefix
   * @param rep the symbol attached to this node
   * @param args the children attached to this node
   */
  public CPred(final boolean pref, final String rep, final STerm [] args) {
    super(pref, rep, args);
  }

  /**
   * Constructs a formula of type pred where its symbol is 
   * considered as prefix.
   * @param rep the symbol attached to this node
   * @param args the children of the node
   */
  public CPred(final String rep, final STerm [] args) {
    super(true, rep, args);
  }

  /**
   * Constructs a formula which has no child attached to it.
   * @param rep the symbol attached to the node
   */
  public CPred(final String rep) {
    super(false, rep, new STerm[0]);
  }

  /**
   * Constructs a formula which has 2 children.
   * @param b tells if the symbol is prefix or not
   * @param rep the symbol attached to the node
   * @param t1 the first child
   * @param t2 the second child
   */
  public CPred(final boolean b, final String rep, final STerm t1, final STerm t2) {
    this(b, rep, new STerm [] {t1, t2});
  }
}
