package freeboogie.backend;

import freeboogie.ast.PrimitiveType;
import freeboogie.ast.Type;
import freeboogie.tc.TypeUtils;

/**
 * The sorts we use to inform the prover about Boogie types.
 *
 * Boogie 'bool' maps to prover booleans; Boogie 'int' maps to
 * prover integers. All other Boogie types have sort 'value'.
 *
 * @author rgrig 
 */
public enum Sort {
  /** supertype for all non-predicates */ VALUE(null),
  /** a variable with unknown sort */ VARVALUE(VALUE),
  /** a boolean value */ BOOL(VALUE),
  /** a boolean variable */ VARBOOL(BOOL),
  /** an integer */ INT(VALUE),
  /** an integer variable */ VARINT(INT);
  
  
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
    return VALUE;
  }
}
