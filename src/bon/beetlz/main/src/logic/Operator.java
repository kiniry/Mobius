package logic;

/**
 * Enumerated operators.
 * They may not be all in use at the moment, but for future use
 * include all possibilities so far. JML has additional operators,
 * however those cannot be used as not present in BON.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public enum Operator {
  /** Universal quantification. */
  FOR_ALL(1, "for_all", "\forall"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Existential quantification. */
  EXISTS(1, "exists", "\\exists"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Member access. */
  DOT(3, ".", "."), //$NON-NLS-1$ //$NON-NLS-2$
  /** Methods call. */
  CALL(3, "()", "()"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Array access. */
  ARRAY_ACCESS(3, "[]", "[]"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Unary plus, ie positive sign. */
  UNARY_PLUS(5, "+", "+"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Unary minus, ie negative sign. */
  UNARY_MINUS(5, "-", "-"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Negation. */
  NOT(5, "not", "!"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Power operator. */
  POWER(10, "^", "Math.pow"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Multiplication. */
  MULTIPLE(15, "*", "*"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Division. */
  DIVIDE(15, "/", "/"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Integer division. */
  INT_DIVIDE(15, "//", "/"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Modulo operator. */
  MODULO(15, "\\\\", "%"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Addition. */
  PLUS(20, "+", "+"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Subtraction. */
  MINUS(20, "-", "-"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Strict inequality greater. */
  GREATER(25, ">", ">"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Strict inequality smaller. */
  SMALLER(25, "<", "<"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Inequality greater. */
  GREATER_EQUAL(25, ">=", ">="), //$NON-NLS-1$ //$NON-NLS-2$
  /** Inequality smaller. */
  SMALLER_EQUAL(25, "<=", "<="), //$NON-NLS-1$ //$NON-NLS-2$
  /** Equality. */
  EQUAL(30, "=", "=="), //$NON-NLS-1$ //$NON-NLS-2$
  /** Inequation. */
  NOT_EQUAL(30, "/=", "!="), //$NON-NLS-1$ //$NON-NLS-2$
  /** Exclusive or. */
  XOR(33, "xor", "^"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Logical conjuction. */
  AND(35, "and", "&&"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Logical disjunction. */
  OR(35, "or", "||"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Implication. */
  IMPLIES(40, "->", "->"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Equivalence. */
  IFF(45, "<->", "<==>"), //$NON-NLS-1$ //$NON-NLS-2$
  /** Negated equivalence. */
  NOT_IFF(45, "<->", "<=!=>"); //$NON-NLS-1$ //$NON-NLS-2$


  /** Holds the type. */
  private final int my_prec;
  /**  */
  private final String my_bonName;
  /**  */
  private final String my_javaName;


  /**
   *
   * @param a_precedence precedence of operator
   * @param a_bon_name bon name
   * @param a_java_name java name
   */
  Operator(final int a_precedence, final String a_bon_name, final String a_java_name) {
    my_prec = a_precedence;
    my_bonName = a_bon_name;
    my_javaName = a_java_name;

  }

  /**
   * Get the Java representation.
   * @return string
   */
  public final String getJavaName() {
    return my_javaName;
  }

  /**
   * Get the Bon representation.
   * @return string
   */
  public final String getBonName() {
    return my_bonName;
  }

  /**
   * Get the precedence of this operator.
   * @return value of precedence
   */
  public final int getPrecedence() {
    return my_prec;
  }

  /**
   * Compare two operators.
   * @param an_other operator to compare to
   * @return 0 if equal
   */
  public final int compareToTyped(final Operator an_other) {
    if (this == an_other) {
      return BeetlzExpression.EQUAL;
    } else {
      return BeetlzExpression.DIFF;
    }
  }
}
