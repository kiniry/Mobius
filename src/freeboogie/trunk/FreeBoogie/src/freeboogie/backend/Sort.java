package freeboogie.backend;

import freeboogie.ast.Type;
import freeboogie.tc.TypeUtils;

/**
 * The sorts we use to inform the prover about Boogie types.
 *
 * Boogie 'int' maps to Sort.INT.
 * Boogie 'bool' maps to Sort.BOOL. This may map to formulas or to terms.
 * Boogie axioms map to Sort.PRED. This maps to formulas.
 * 
 * Provers have formulas that evaluate to true/false if all their
 * variables are bound and terms that are just 'stuff'. Uninterpreted
 * functions can *only* be applied to terms to give another term.
 * Some provers allow the constructions of terms out of formulas
 * (those that read SMT) but some don't (Simplify): (ite true/false t1 t2).
 *
 * @author rgrig 
 */
public enum Sort {
  FORMULA(null),
  VARFORMULA(FORMULA),
  TERM(null),
  VARTERM(TERM),
  BOOL(TERM),
  VARBOOL(BOOL),
  INT(TERM),
  VARINT(INT);
  
  
  /* Note: The VARx sorts are used for better checking of quantifiers.
   * That is, in some places you want to enforce that you have a variable
   * of a certain type, not just an expression.
   */
  
  /** The supersort of {@code this}. */
  public final Sort superSort;

  /**
   * Constructs a sort, with a given super sort.
   * @param superSort the super sort
   */
  Sort(Sort superSort) {
    this.superSort = superSort;
  }
  
  /**
   * Tests whether {@code this} is a subsort of {@code other}.
   * @param other the potential supersort
   * @return whether {@code this <: other}
   */
  public boolean isSubsortOf(Sort other) {
    if (this == other) return true;
    if (superSort == null) return false;
    return superSort.isSubsortOf(other);
  }

  /** Returns a sort corresponding to a given Boogie type. */
  public static Sort of(Type t) {
    // TODO keep more information in the sort?
    if (TypeUtils.isInt(t)) return INT;
    else if (TypeUtils.isBool(t)) return BOOL;
    return TERM;
  }
}
