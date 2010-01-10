package logic;

import java.util.List;

import main.Beetlz;
import utils.BConst;
import utils.BasicTypesDictionary;
import utils.smart.FeatureSmartString;
import utils.smart.SmartString;

/**
 * Abstract class for assertion expression.
 * Each type of expression has its own class.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public abstract class BeetlzExpression {
  /** Value for equal in comparisons. */
  public static final int EQUAL = 0;
  /** Value for small difference in comparisons. */
  public static final int DIFF = 1;
  /** Value for big difference in comparison. */
  public static final int VERY_DIFF = 100;
  /**  */
  public static enum Nullity { NON_NULL, NULLABLE };

  /**  */
  private static BasicTypesDictionary assertionDict =
    Beetlz.getProfile().getAssertionDictionary();

  /**  */
  private boolean my_parentheses;

  /**  */
  private static final String SPACE = " "; //$NON-NLS-1$

  /**
   * Create new expression.
   * @param the_parens true if expression has parenthesis around it
   */
  public BeetlzExpression(final boolean the_parens) {
    my_parentheses = the_parens;
  }

  /**
   * Compare to expression for logical equivalence.
   * If they are equal, return 0.
   * If they are 'almost' equal, return +1.
   * If they are not at all equal, return +100.
   * Note: the positive values are ABSOLUTELY NECESSARY, or we get junk.
   * @param an_other expression to compare to
   * @return 0 if equal
   */
  public abstract int compareToTyped(BeetlzExpression an_other);

  /**
   * Whether to skip this expression during comparison.
   * This may be the case for example if the expression contains
   * informal expressions.
   * @return true if contains an informal expression
   */
  public abstract boolean skip();

  /**
   * Print Bon type string.
   * @return string representation
   */
  public String toBonString() {
    if (my_parentheses) {
      return "(" + toBonStringSimple() + ")"; //$NON-NLS-1$ //$NON-NLS-2$
    } else
      return toBonStringSimple();
  }

  /**
   * Print Java type string.
   * @return string representation
   */
  public String toJavaString() {
    if (my_parentheses) {
      return "(" + toJavaStringSimple() + ")"; //$NON-NLS-1$ //$NON-NLS-2$
    } else
      return toJavaStringSimple();
  }

  /**
   * Are the two expressions of the same type.
   * Shortcut mainly.
   * @param an_other expression to compare type to
   * @return true if of the same class type
   */
  public boolean sameType(final BeetlzExpression an_other) {
    return an_other.getClass().equals(this.getClass());
  }

  /**
   * Check if the expression has parethesis around it.
   * @return true if parentheses present
   */
  public final boolean isParenthesised() {
    return my_parentheses;
  }

  /**
   * Set parentheses around this expression.
   */
  public final void setParenthesised() {
    my_parentheses = true;
  }

  /**
   * Print Bon.
   * @return string
   */
  public abstract String toBonStringSimple();

  /**
   * Print Java.
   * @return string
   */
  public abstract String toJavaStringSimple();

  /**
   * Different valid keywords.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class Keyword extends BeetlzExpression {
    /** Keywords accepted. */
    public enum Keywords {
      /** Current or this keyword. */
      CURRENT ("Current", "this"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Result or \result keyword. */
      RESULT("Result", "\\result"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Void. */
      VOID("Void", "void"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Null. */
      NULL("Void", "null"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Old or \old. */
      OLD("old", "\\old"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Non-null. */
      NON_NULL("", "non_null"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Nullable. */
      NULLABLE("", "nullable"),  //$NON-NLS-1$ //$NON-NLS-2$
      /** Nullable-by-default, for classes. */
      NULLABLE_DEFAULT("", "nullable_by_default"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Non-null-elements for arrays. */
      NONNULL_ELEMENTS("", "\\nonnullelements"), //$NON-NLS-1$ //$NON-NLS-2$
      /** \nothing. */
      NOTHING("\\nothing", "\\nothing"), //$NON-NLS-1$ //$NON-NLS-2$
      /** \everything. */
      EVERYTHING("\\everything", "\\everything"), //$NON-NLS-1$ //$NON-NLS-2$
      /** \not_specified. */
      NOT_SPECIFIED("\\not_specified", "\\not_specified"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Boolean true. */
      TRUE("true", "true"), //$NON-NLS-1$ //$NON-NLS-2$
      /** Boolean false. */
      FALSE("false", "false"); //$NON-NLS-1$ //$NON-NLS-2$

      /** Holds the type. */
      private final String my_bonName;
      /**  */
      private final String my_javaName;

      /**
       * Create a keyword.
       * @param a_bon_name bon name
       * @param a_java_name java name
       */
      private Keywords(final String a_bon_name, final String a_java_name) {
        my_bonName = a_bon_name;
        my_javaName = a_java_name;
      }

    } //end enum

    /**  */
    private final Keywords my_keyword;

    /**
     * Create a new keyword.
     * @param a_key keyword
     */
    public Keyword(final Keywords a_key) {
      super(false);
      my_keyword = a_key;

    }

    /**
     * Get Java representation.
     * @return string
     */
    public final String getJavaName() {
      return my_keyword.my_javaName;
    }

    /**
     * Get Bon representation. string
     * @return string
     */
    public final String getBonName() {
      return my_keyword.my_bonName;
    }

    /**
     * Compare to expression for logical equivalence.
     * If they are equal, return 0.
     * If they are 'almost' equal, return +1.
     * If they are not at all equal, return +100.
     * Note: the positive values are ABSOLUTELY NECESSARY, or we get junk.
     * @param an_other expression to compare to
     * @return 0 if equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof Keyword) {
        final Keyword k = (Keyword) an_other;
        if (my_keyword == k.my_keyword) {
          return BeetlzExpression.EQUAL;
        }
        if (my_keyword == Keywords.VOID && k.my_keyword == Keywords.NULL) {
          return BeetlzExpression.EQUAL;
        }
        if (my_keyword == Keywords.NULL && k.my_keyword == Keywords.VOID) {
          return BeetlzExpression.EQUAL;
        } else {
          return BeetlzExpression.DIFF;
        }
      } else {
        return BeetlzExpression.VERY_DIFF;
      }
    }

   
    
    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return false;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_keyword.my_javaName;
    }

    /**
     * Bon type string representation.
     * @see logic.BeetlzExpression#toBonString()
     * @return string
     */
    @Override
    public final String toBonStringSimple() {
      return my_keyword.my_bonName;
    }

    /**
     * Get Java representation.
     * @return string
     */
    @Override
    public final String toJavaStringSimple() {
      return my_keyword.my_javaName;
    }
  } //end Keyword


  /**
   * Equality expressions that is 'equal' and 'not equal'.
   * Equality expressions are symmetric.
   * Note the difference between equivalence expressions.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class EqualityExpression extends BeetlzExpression {
    /**  */
    private final BeetlzExpression my_left;
    /**  */
    private final BeetlzExpression my_right;
    /**  */
    private final Operator my_op;

    /**
     * Create a new equality expression.
     * @param a_lhs left operand
     * @param an_op operator
     * @param a_rhs right operand
     */
    public EqualityExpression(final BeetlzExpression a_lhs, final Operator an_op,
                              final BeetlzExpression a_rhs) {
      super(false);
      my_left = a_lhs;
      my_right = a_rhs;
      my_op = an_op;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_left.toString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof EqualityExpression) {
        final EqualityExpression other = (EqualityExpression) an_other;
        final int one = my_left.compareToTyped(other.my_left) +
          my_op.compareToTyped(other.my_op) + my_right.compareToTyped(other.my_right);
        final int two = my_left.compareToTyped(other.my_right) +
          my_op.compareToTyped(other.my_op) + my_right.compareToTyped(other.my_left);
        if (one == BeetlzExpression.EQUAL || two == BeetlzExpression.EQUAL) {
          return BeetlzExpression.EQUAL;
        }
        return one;
      }
      //not ( ... = ... )
      if (an_other instanceof UnaryExpression) {
        final UnaryExpression other = (UnaryExpression) an_other;
        if (other.my_op == Operator.NOT && other.my_expr instanceof EqualityExpression) {
          final EqualityExpression eqExpr = (EqualityExpression) other.my_expr;
          Operator eq_op;
          if (eqExpr.my_op == Operator.EQUAL) eq_op = Operator.NOT_EQUAL;
          else eq_op = Operator.EQUAL;
          final int one = my_left.compareToTyped(eqExpr.my_left) +
            my_op.compareToTyped(eq_op) + my_right.compareToTyped(eqExpr.my_right);
          final int two = my_left.compareToTyped(eqExpr.my_right) +
            my_op.compareToTyped(eq_op) + my_right.compareToTyped(eqExpr.my_left);
          if (one == BeetlzExpression.EQUAL || two == BeetlzExpression.EQUAL) {
            return BeetlzExpression.EQUAL;
          }
          return one;
        }
        if (other.my_op == Operator.NOT && other.my_expr instanceof MethodcallExpression) {
          Operator eq_op;
          if (my_op == Operator.EQUAL) eq_op = Operator.NOT_EQUAL;
          else eq_op = Operator.EQUAL;
          return other.my_expr.
          compareToTyped(new EqualityExpression(my_left, eq_op, my_right));
        }
      }
      if (an_other instanceof MethodcallExpression) {
        final MethodcallExpression methodCall = (MethodcallExpression) an_other;
        if (methodCall.my_method instanceof MemberaccessExpression &&
            methodCall.my_arguments.size() == 1) {
          final MemberaccessExpression memAccess =
            (MemberaccessExpression) methodCall.my_method;
          if (memAccess.my_field.toString().equals("equals")) { //$NON-NLS-1$
            return compareToTyped(new EqualityExpression(memAccess.my_source,
                                                              Operator.EQUAL,
                                                              methodCall.my_arguments.get(0)));
          }
        }
      }
      return BeetlzExpression.VERY_DIFF;
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_left.skip() || my_right.skip();
    }

    /**
     * Get left operand.
     * @return left expression operand
     */
    public BeetlzExpression getLeft() {
      return my_left;
    }

    /**
     * Get right operand.
     * @return right expression operand
     */
    public BeetlzExpression getRight() {
      return my_right;
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toBonString()
     * @return string
     */
    @Override
    public final String toBonStringSimple() {
      return my_left.toBonString() + SPACE + my_op.getBonName() +
        SPACE +  my_right.toBonString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_left.toJavaString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toJavaString();
    }
  } //end Equality Expr

  /**
   * Arithmetic expressions.
   * Plus and multiply operations are symmetric,
   * division, modulo and subtraction are not.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   *
   */
  public static class ArithmeticExpression extends BeetlzExpression {
    /**  */
    private final BeetlzExpression my_left;
    /**  */
    private final BeetlzExpression my_right;
    /**  */
    private final Operator my_op;

    /**
     * Create a new Arithemetic expression.
     * It is not checked, whether the operand is admissible.
     * @param a_lhs left operand
     * @param an_op operator
     * @param a_rhs right operand
     */
    public ArithmeticExpression(final BeetlzExpression a_lhs,
                                final Operator an_op,
                                final BeetlzExpression a_rhs) {
      super(false);
      my_left = a_lhs;
      my_right = a_rhs;
      my_op = an_op;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_left.toString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      final int twoNumber = 2;
      if (an_other instanceof ArithmeticExpression) {
        final ArithmeticExpression other = (ArithmeticExpression) an_other;
        if (my_op == Operator.PLUS) {
          final int one = my_left.compareToTyped(other.my_left) +
            my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_right);
          final int two = my_left.compareToTyped(other.my_right) +
            my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_left);
          if (one == 0 || two == 0) {
            return BeetlzExpression.EQUAL;
          } else {
            return one;
          }
        }
        if (my_op == Operator.MINUS) {
          return my_left.compareToTyped(other.my_left) + my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_right);
        }
        if (my_op == Operator.MULTIPLE) {
          final int one = my_left.compareToTyped(other.my_left) +
            my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_right);
          final int two = my_left.compareToTyped(other.my_right) +
            my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_left);
          if (one == 0 || two == 0) {
            return BeetlzExpression.EQUAL;
          } else {
            return one;
          }
        }
        if (my_op == Operator.DIVIDE) {
          return my_left.compareToTyped(other.my_left) + my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_right);
        }
        if (my_op == Operator.MODULO) {
          return my_left.compareToTyped(other.my_left) + my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_right);
        }
        if (my_op == Operator.POWER) {
          return my_left.compareToTyped(other.my_left) + my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_right);
        }
      }
      if (my_op == Operator.POWER && an_other instanceof MethodcallExpression) {
        final MethodcallExpression methodCall = (MethodcallExpression) an_other;
        if (methodCall.my_method instanceof MemberaccessExpression &&
            methodCall.my_arguments.size() == twoNumber) {
          final MemberaccessExpression memAccess =
            (MemberaccessExpression) methodCall.my_method;
          if (memAccess.my_field.toString().equals("pow") &&  //$NON-NLS-1$
              memAccess.my_source.toString().equals("Math")) { //$NON-NLS-1$
            return my_left.compareToTyped(methodCall.my_arguments.get(0)) +
            my_right.compareToTyped(methodCall.my_arguments.get(1));
          }
        }
      }
      return BeetlzExpression.VERY_DIFF;
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_left.skip() || my_right.skip();
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      return my_left.toBonString() + SPACE + my_op.getBonName() +
        SPACE + my_right.toBonString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      if (my_op == Operator.POWER) {
        return "Math.pow(" + my_left.toJavaString() + ", " + //$NON-NLS-1$ //$NON-NLS-2$
          my_right.toJavaString() + ")";  //$NON-NLS-1$
      }
      if (my_op == Operator.INT_DIVIDE) {
        return "(int)" + SPACE + my_left.toJavaString() + //$NON-NLS-1$
          SPACE + my_op.getJavaName() +
          " (int)" + SPACE + my_right.toJavaString(); //$NON-NLS-1$
      }
      return my_left.toJavaString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toJavaString();
    }
  } //end Arithmetic expr


  /**
   * Array access.
   * In BON this is equal to a method call on a data structure.
   * The operation is not symmetric.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class ArrayaccessExpression extends BeetlzExpression {
    /** */
    private final BeetlzExpression my_array;
    /** */
    private final BeetlzExpression my_index;

    /**
     * Create a new array access expression.
     * @param an_array array name
     * @param an_index index expression, does not have to a number
     */
    public ArrayaccessExpression(final BeetlzExpression an_array, final BeetlzExpression an_index) {
      super(false);
      my_array = an_array;
      my_index = an_index;
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public String toString() {
      return my_array.toString() + "[" + my_index.toString() + "]"; //$NON-NLS-1$ //$NON-NLS-2$
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof ArrayaccessExpression) {
        final ArrayaccessExpression other = (ArrayaccessExpression) an_other;
        return  my_array.compareToTyped(other.my_array) +
        my_index.compareToTyped(other.my_index);
      }
      if (an_other instanceof MethodcallExpression) {
        final MethodcallExpression other = (MethodcallExpression) an_other;
        if (other.my_method instanceof MemberaccessExpression &&
            other.my_arguments.size() == 1) {
          final MemberaccessExpression mem = (MemberaccessExpression) other.my_method;
          if (mem.my_field.toString().equals("item")) { //$NON-NLS-1$
            return my_array.compareToTyped(mem.my_source) +
            my_index.compareToTyped(other.my_arguments.get(0));
          }
        }
      }
      return BeetlzExpression.VERY_DIFF;
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_array.skip() || my_index.skip();
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      return my_array + "." + BConst.BON_ARRAY_ACCESS +  //$NON-NLS-1$
        "(" + my_index + ")"; //$NON-NLS-1$ //$NON-NLS-2$
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_array.toJavaString() + "[" + my_index.toJavaString() + //$NON-NLS-1$
        "]";  //$NON-NLS-1$
    }
  } //end Array access

  /**
   * Logical equivalence or 'if and only if' expression.
   * These expressions are symmetric.
   * @author evka
   *
   */
  public static class EquivalenceExpression extends BeetlzExpression {
    /**  */
    private final BeetlzExpression my_left;
    /**  */
    private final BeetlzExpression my_right;
    /**  */
    private final Operator my_op;

    /**
     * Create a new equivalence expression.
     * @param a_lhs left operand
     * @param an_op operator
     * @param a_rhs right operand
     */
    public EquivalenceExpression(final BeetlzExpression a_lhs,
                                 final Operator an_op,
                                 final BeetlzExpression a_rhs) {
      super(false);
      my_left = a_lhs;
      my_right = a_rhs;
      my_op = an_op;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_left.toString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof EquivalenceExpression) {
        final EquivalenceExpression other = (EquivalenceExpression) an_other;
        final int one = my_left.compareToTyped(other.my_left) +
          my_op.compareToTyped(other.my_op) +
          my_right.compareToTyped(other.my_right);
        final int two = my_left.compareToTyped(other.my_right) +
          my_op.compareToTyped(other.my_op) +
          my_right.compareToTyped(other.my_left);
        if (one == BeetlzExpression.EQUAL || two == BeetlzExpression.EQUAL) {
          return BeetlzExpression.EQUAL;
        }
        return one;
      }
      if (an_other instanceof UnaryExpression) {
        final UnaryExpression other = (UnaryExpression) an_other;
        if (other.my_op == Operator.NOT && other.my_expr instanceof EquivalenceExpression) {
          final EquivalenceExpression eqExpr = (EquivalenceExpression) other.my_expr;
          Operator eq_op;
          if (eqExpr.my_op == Operator.IFF) eq_op = Operator.NOT_IFF;
          else eq_op = Operator.IFF;
          final int one = my_left.compareToTyped(eqExpr.my_left) +
            my_op.compareToTyped(eq_op) + my_right.compareToTyped(eqExpr.my_right);
          final int two = my_left.compareToTyped(eqExpr.my_right) +
            my_op.compareToTyped(eq_op) + my_right.compareToTyped(eqExpr.my_left);
          if (one == BeetlzExpression.EQUAL || two == BeetlzExpression.EQUAL) {
            return BeetlzExpression.EQUAL;
          }
          return one;
        }
      }
      return BeetlzExpression.VERY_DIFF;
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_left.skip() || my_right.skip();
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      if (my_op == Operator.NOT_IFF) {
        return "not ( " + my_left.toBonString() + SPACE +  //$NON-NLS-1$
          Operator.IFF.getBonName() +
          SPACE + my_right.toBonString() + SPACE + ")"; //$NON-NLS-1$
      }
      return my_left.toBonString() + SPACE + my_op.getBonName() +
        SPACE + my_right.toBonString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_left.toJavaString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toJavaString();
    }
  }  //end Equivalence expr

  /**
   * Implies expression.
   * This expression is not symmetric. A reverse-implies expression
   * exists in Java, for which it holds: if a -> b , then b <- a.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class ImpliesExpression extends BeetlzExpression {
    /** */
    private final BeetlzExpression my_left;
    /** */
    private final BeetlzExpression my_right;
    /** */
    private final Operator my_op;

    /**
     * Create a new implication expression.
     * @param a_lhs left operand
     * @param a_rhs rigth operand
     */
    public ImpliesExpression(final BeetlzExpression a_lhs, final BeetlzExpression a_rhs) {
      super(false);
      my_left = a_lhs;
      my_right = a_rhs;
      my_op = Operator.IMPLIES;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_left.toString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof ImpliesExpression) {
        final ImpliesExpression other = (ImpliesExpression) an_other;
        return my_left.compareToTyped(other.my_left) + my_right.compareToTyped(other.my_right);
      } else {
        return BeetlzExpression.VERY_DIFF;
      }
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_left.skip() || my_right.skip();
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      return my_left.toBonString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toBonString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_left.toJavaString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toJavaString();
    }
  } //end Implies expr

  /**
   * An informal expression.
   * This can hold an originally informal predicate,
   * or it can hold a predicate
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class InformalExpression extends BeetlzExpression {
    /** An empty informal expression, this happens in JML.*/
    public static final InformalExpression EMPTY_COMMENT =
      new InformalExpression(" ... "); //$NON-NLS-1$
    /** */
    private final String my_informal;

    /**
     * Create a new informal expression.
     * @param an_expr message
     */
    public InformalExpression(final String an_expr) {
      super(false);
      my_informal = an_expr;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return "(*" + SPACE + my_informal + SPACE + "*)"; //$NON-NLS-1$ //$NON-NLS-2$
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof InformalExpression) {
        final InformalExpression a_inf = (InformalExpression) an_other;
        if (my_informal.compareTo(a_inf.my_informal) == 0) {
          return BeetlzExpression.EQUAL;
        } else {
          return BeetlzExpression.DIFF;
        }
      }
      return BeetlzExpression.VERY_DIFF;
    }

   /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return true;
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      return my_informal;
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_informal;
    }
  } //end Informal expr

  /**
   * Represents an identifier such as a method or variable name.
   * When comparing it takes into account different naming conventions
   * for arrays and lists, such as item() - get() etc.
   * and also prefix conventions defined in a custom settings file.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class IdentifierExpression extends BeetlzExpression {
    /** */
    private final SmartString my_ident;

    /**
     * Create a new identifier expression.
     * @param an_expr type or identifier name
     */
    public IdentifierExpression(final String an_expr) {
      super(false);
      my_ident = new FeatureSmartString(an_expr);
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_ident.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof IdentifierExpression) {
        final IdentifierExpression other = (IdentifierExpression) an_other;
        if (my_ident.compareToTyped(other.my_ident) == 0) {
          return BeetlzExpression.EQUAL;
        }
        if (testWithoutMap(other.my_ident.toString()) ||
            testWithMap(other.my_ident.toString())) {
          return BeetlzExpression.EQUAL;
        }
        return BeetlzExpression.DIFF;
      }
      return BeetlzExpression.VERY_DIFF;
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return false;
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      return my_ident.toString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_ident.toString();
    }

    /**
     * Test for equality with the help of a mapping.
     * @param the_other string to compare to
     * @return true if equal based on mapping
     */
    private boolean testWithMap(final String the_other) {
      final FeatureSmartString map =
        new FeatureSmartString(Beetlz.getProfile().getSimpleFeatureMapping(the_other));
      final FeatureSmartString mapFree =
        new FeatureSmartString(Beetlz.getProfile().
                               getSimpleFeatureMapping(getAccessorFree(the_other)));
      final FeatureSmartString ident =
        new FeatureSmartString(my_ident.toString());
      final FeatureSmartString identFree =
        new FeatureSmartString(getAccessorFree(my_ident.toString()));

      if (map != null && (ident.equalsTyped(map) || identFree.equalsTyped(map))) {
        return true;
      }
      if (mapFree != null && (ident.equalsTyped(mapFree) || identFree.equalsTyped(mapFree))) {
        return true;
      }
      return false;
    }

    /**
     * Test for equality without mapping.
     * @param the_other string to compare to
     * @return true if equal literally
     */
    private boolean testWithoutMap(final String the_other) {
      final FeatureSmartString map =
        new FeatureSmartString(the_other);
      final FeatureSmartString mapFree =
        new FeatureSmartString(getAccessorFree(the_other));
      final FeatureSmartString ident =
        new FeatureSmartString(my_ident.toString());
      final FeatureSmartString identFree =
        new FeatureSmartString(getAccessorFree(my_ident.toString()));

      if (ident.equalsTyped(map) || identFree.equalsTyped(map)) {
        return true;
      }
      if (ident.equalsTyped(mapFree) || identFree.equalsTyped(mapFree)) {
        return true;
      }
      return false;
    }

    /**
     * Get the string without accessor prefixes.
     * @param the_string original string
     * @return string without get-, has-, is-, set- prefixes
     */
    private String getAccessorFree(final String the_string) {
      final int two = 2;
      final int three = 3;
      String one;
      if (the_string.startsWith(BConst.METHOD_GET) ||
          the_string.startsWith(BConst.METHOD_HAS)) {
        one = the_string.substring(three);
      } else if (the_string.startsWith(BConst.METHOD_IS)) {
        one = the_string.substring(two);
      } else {
        one = the_string;
      }
      one = one.substring(0, 1).toLowerCase() + one.substring(1);
      return one;
    }
  }

  /**
   * Represents a literal expression, such as strings, numbers or
   * method names.
   * Literals are numbers and literal strings like "...".
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class LiteralExpression extends BeetlzExpression {
    /** */
    private final SmartString my_literal;

    /**
     * Create a new Literal expression.
     * @param an_expr expression literal
     */
    public LiteralExpression(final String an_expr) {
      super(false);
      my_literal = new SmartString(an_expr);
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_literal.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof LiteralExpression) {
        final LiteralExpression a_lit = (LiteralExpression) an_other;
        if (my_literal.compareToTyped(a_lit.my_literal) == 0) {
          return BeetlzExpression.EQUAL;
        } else {
          return BeetlzExpression.DIFF;
        }
      }
      return BeetlzExpression.VERY_DIFF;
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return false;
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      return my_literal.toString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_literal.toString();
    }
  } //end Literal expr

  /**
   * Represents expressions with AND, OR, XOR.
   * The order of operands does matter for and and or,
   * since they are semi-strict.
   * Xor is symmetric.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class LogicalExpression extends BeetlzExpression {
    /** */
    private final BeetlzExpression my_left;
    /** */
    private final BeetlzExpression my_right;
    /** */
    private final Operator my_op;

    /**
     * Create a new logical expression.
     * @param a_lhs left operand
     * @param an_op operator
     * @param a_rhs right operand
     */
    public LogicalExpression(final BeetlzExpression a_lhs, final Operator an_op,
                             final BeetlzExpression a_rhs) {
      super(false);
      my_left = a_lhs;
      my_right = a_rhs;
      my_op = an_op;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_left.toString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof LogicalExpression) {
        final LogicalExpression other = (LogicalExpression) an_other;
        //xor symmetric
        if (other.my_op == Operator.XOR) {
          final int one = my_left.compareToTyped(other.my_left) +
            my_op.compareToTyped(other.my_op) +
            my_right.compareToTyped(other.my_right);
          final int two = my_left.compareToTyped(other.my_right) +
            my_op.compareToTyped(other.my_op) + my_right.compareToTyped(other.my_left);
          if (one == BeetlzExpression.EQUAL || two == BeetlzExpression.EQUAL) {
            return BeetlzExpression.EQUAL;
          }
          return one;
        }
        //And, or
        return my_left.compareToTyped(other.my_left) + my_op.compareToTyped(other.my_op) +
          my_right.compareToTyped(other.my_right);
      } else {
        return BeetlzExpression.VERY_DIFF;
      }
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_left.skip() || my_right.skip();
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      return my_left.toBonString() + SPACE + my_op.getBonName() +
        SPACE + my_right.toBonString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_left.toJavaString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toJavaString();
    }

    /**
     * Get the left operand.
     * @return left expression operand
     */
    public BeetlzExpression leftExpression() {
      return my_left;
    }

    /**
     * Get right operand.
     * @return right expression operand
     */
    public BeetlzExpression rightExpression() {
      return my_right;
    }

    /**
     * Get the operator.
     * @return operator
     */
    public Operator getOperator() {
      return my_op;
    }
  } //end Logical expr

  /**
   * Expression for member/ feature access.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class MemberaccessExpression extends BeetlzExpression {
    /** */
    private final BeetlzExpression my_source;
    /** */
    private final BeetlzExpression my_field;
    /** */
    private final Operator my_op;

    /**
     * Create a new member access expression.
     * @param a_source member
     * @param a_field field of member
     */
    public MemberaccessExpression(final BeetlzExpression a_source, final BeetlzExpression a_field) {
      super(false);
      my_source = a_source;
      my_field = a_field;
      my_op = Operator.DOT;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_source.toString() + SPACE + my_op.getJavaName() +
        SPACE + my_field.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof MemberaccessExpression) {
        final MemberaccessExpression other = (MemberaccessExpression) an_other;
        final int srcScore = my_source.compareToTyped(other.my_source);
        int field_score = my_field.compareToTyped(other.my_field);
        if (field_score != BeetlzExpression.EQUAL &&
            (other.my_field instanceof IdentifierExpression) &&
            my_field instanceof IdentifierExpression) {
          final boolean map = assertionDict.matchTypes(my_field.toString(),
                                                       other.my_field.toString());
          if (map) field_score = BeetlzExpression.EQUAL;
        }
        return srcScore + field_score;
      }
      if (an_other instanceof MethodcallExpression) {
        return an_other.compareToTyped(this);
      }
      return BeetlzExpression.VERY_DIFF;

    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_source.skip() || my_field.skip();
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      if (my_field instanceof IdentifierExpression) {
        final IdentifierExpression l = (IdentifierExpression) my_field;
        final String map = assertionDict.getJavaToBonMapping(l.toBonStringSimple());
        if (map != null) {
          return my_source.toBonString() + my_op.getBonName() + map;
        }
      }
      return my_source.toBonString() + my_op.getBonName() + my_field.toBonString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_source.toJavaString() + SPACE + my_op.getJavaName() +
        SPACE + my_field.toJavaString();
    }
  } //end Memberaccess expr

  /**
   * Method call expression.
   * Sometimes a no-argument method call is equivalent to a simple
   * member access, so that this has to be considered.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class MethodcallExpression extends BeetlzExpression {
    /** */
    private final BeetlzExpression my_method;
    /** */
    private final List < BeetlzExpression > my_arguments;

    /**
     * Create a new method call expression.
     * @param a_method method name
     * @param the_arguments call arguments
     */
    public MethodcallExpression(final BeetlzExpression a_method,
                                final List < BeetlzExpression > the_arguments) {
      super(false);
      my_method = a_method;
      my_arguments = the_arguments;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      String args = ""; //$NON-NLS-1$
      if (my_arguments.size() > 0) {
        for (int i = 0; i < my_arguments.size() - 1; i++) {
          args += my_arguments.get(i) + "," + SPACE; //$NON-NLS-1$
        }
        args += my_arguments.get(my_arguments.size() - 1);
      }
      return my_method.toString() + "(" + my_arguments + ")"; //$NON-NLS-1$ //$NON-NLS-2$
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof MethodcallExpression) {
        final MethodcallExpression other = (MethodcallExpression) an_other;
        int sum = my_method.compareToTyped(other.my_method);
        if (my_arguments.size() == other.my_arguments.size()) {
          for (int i = 0; i < my_arguments.size(); i++) {
            sum += my_arguments.get(i).compareToTyped(other.my_arguments.get(i));
          }
          return sum;
        } else {
          return BeetlzExpression.DIFF + sum;
        }
      }
      if (an_other instanceof ArrayaccessExpression) {
        return an_other.compareToTyped(this);
      }
      if (an_other instanceof MemberaccessExpression && my_arguments.size() == 0) {
        return my_method.compareToTyped(an_other);
      }
      if (an_other instanceof EqualityExpression) {
        return an_other.compareToTyped(this);
      }
      if (an_other instanceof ArithmeticExpression) {
        return an_other.compareToTyped(this);
      }
      return BeetlzExpression.VERY_DIFF;
    }


    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      for (final BeetlzExpression e : my_arguments) {
        if (e.skip()) {
          return true;
        }
      }
      return my_method.skip();
    }


    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      //Case: Math.pow
      final int twoNumber = 2;
      if (my_method instanceof MemberaccessExpression &&
          my_arguments.size() == twoNumber) {
        final MemberaccessExpression memAccess = (MemberaccessExpression) my_method;
        if (memAccess.my_field.toString().equals("pow") &&  //$NON-NLS-1$
            memAccess.my_source.toString().equals("Math")) { //$NON-NLS-1$
          return my_arguments.get(0) + SPACE + Operator.POWER.getBonName() +
            SPACE + my_arguments.get(1);
        }
      }
      //Case: equals
      if (my_method instanceof MemberaccessExpression &&
          my_arguments.size() == 1) {
        final MemberaccessExpression memAccess = (MemberaccessExpression) my_method;
        if (memAccess.my_field.toString().equals("equals")) { //$NON-NLS-1$
          return memAccess.my_source.toBonString() + SPACE + Operator.EQUAL.getBonName() +
            SPACE + my_arguments.get(0);
        }
      }
      //Anything else
      String args = ""; //$NON-NLS-1$
      if (my_arguments.size() > 0) {
        for (int i = 0; i < my_arguments.size() - 1; i++) {
          args += my_arguments.get(i).toBonString() + "," + SPACE; //$NON-NLS-1$
        }
        args += my_arguments.get(my_arguments.size() - 1).toBonString();
      }
      if (args.length() == 0) {
        return my_method.toBonString();
      }
      return my_method.toBonString() + "(" + args + ")"; //$NON-NLS-1$ //$NON-NLS-2$
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      String args = ""; //$NON-NLS-1$
      if (my_arguments.size() > 0) {
        for (int i = 0; i < my_arguments.size() - 1; i++) {
          args += my_arguments.get(i).toJavaString() + "," + SPACE; //$NON-NLS-1$
        }
        args += my_arguments.get(my_arguments.size() - 1).toJavaString();
      }

      if (my_method.toString().equals("old")) { //$NON-NLS-1$
        return "\\old" + "(" + args + ")"; //$NON-NLS-1$ //$NON-NLS-2$ //$NON-NLS-3$
      }
      return my_method.toJavaString() + "(" + args + ")"; //$NON-NLS-1$ //$NON-NLS-2$
    }
  } //end methodcall expr


  /**
   * Relational expressions.
   * Note a < b is equivalent to b > a, and has to be considered.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class RelationalExpression extends BeetlzExpression {
    /** */
    private final BeetlzExpression my_left;
    /** */
    private final BeetlzExpression my_right;
    /** */
    private final Operator my_op;

    /**
     * Create a new relational expression.
     * @param a_lhs left operand
     * @param an_op operator
     * @param a_rhs right operand
     */
    public RelationalExpression(final BeetlzExpression a_lhs,
                                final Operator an_op,
                                final BeetlzExpression a_rhs) {
      super(false);
      my_right = a_rhs;
      my_left = a_lhs;
      my_op = an_op;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_left.toString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toString();
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof RelationalExpression) {
        final RelationalExpression rel = (RelationalExpression) an_other;
        if (my_op == Operator.GREATER) {
          if (rel.my_op == Operator.GREATER) {
            return my_left.compareToTyped(rel.my_left) + my_right.compareToTyped(rel.my_right);
          } else if (rel.my_op == Operator.SMALLER) {
            return my_left.compareToTyped(rel.my_right) + my_right.compareToTyped(rel.my_left);
          } else {
            return 1;
          }
        //greater
        } else if (my_op == Operator.SMALLER) {
          if (rel.my_op == Operator.SMALLER) {
            return my_left.compareToTyped(rel.my_left) + my_right.compareToTyped(rel.my_right);
          } else if (rel.my_op == Operator.GREATER) {
            return my_left.compareToTyped(rel.my_right) + my_right.compareToTyped(rel.my_left);
          } else {
            return 1;
          }
        //smaller
        } else if (my_op == Operator.GREATER_EQUAL) {
          if (rel.my_op == Operator.GREATER_EQUAL) {
            return my_left.compareToTyped(rel.my_left) + my_right.compareToTyped(rel.my_right);
          } else if (rel.my_op == Operator.SMALLER_EQUAL) {
            return my_left.compareToTyped(rel.my_right) + my_right.compareToTyped(rel.my_left);
          } else {
            return 1;
          }
        //greaterequal
        } else if (my_op == Operator.SMALLER_EQUAL) {
          if (rel.my_op == Operator.SMALLER_EQUAL) {
            return my_left.compareToTyped(rel.my_left) + my_right.compareToTyped(rel.my_right);
          } else if (rel.my_op == Operator.GREATER_EQUAL) {
            return my_left.compareToTyped(rel.my_right) + my_right.compareToTyped(rel.my_left);
          } else {
            return 1;
          }
        //smallerequal
        } else {
          return BeetlzExpression.VERY_DIFF;
        }
      } else {
        return BeetlzExpression.VERY_DIFF;
      }
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_left.skip() || my_right.skip();
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      return my_left.toBonString() + SPACE + my_op.getBonName() +
        SPACE + my_right.toBonString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      return my_left.toJavaString() + SPACE + my_op.getJavaName() +
        SPACE + my_right.toJavaString();
    }
  } //end Relational expr

  /**
   * Unary expressions.
   * The unary operators recognized are +, - and not (! in Java).
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  public static class UnaryExpression extends BeetlzExpression {
    /** */
    private final BeetlzExpression my_expr;
    /** */
    private final Operator my_op;

    /**
     * Create a new unary expression.
     * @param an_op operator
     * @param an_expr expression
     */
    public UnaryExpression(final Operator an_op, final BeetlzExpression an_expr) {
      super(false);
      my_expr = an_expr;
      my_op = an_op;
    }

    /**
     * String representation.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_op.getJavaName() + "(" + //$NON-NLS-1$
      my_expr.toString() + ")";  //$NON-NLS-1$
    }

    /**
     * Compare expressions based on type.
     * @see logic.BeetlzExpression#compareToTyped(logic.BeetlzExpression)
     * @param an_other expression to compare to
     * @return 0 if logically equal
     */
    @Override
    public int compareToTyped(final BeetlzExpression an_other) {
      if (an_other instanceof UnaryExpression) {
        final UnaryExpression other = (UnaryExpression) an_other;
        return my_op.compareToTyped(other.my_op) +
          my_expr.compareToTyped(other.my_expr);
      }
      if (an_other instanceof EqualityExpression) {
        return an_other.compareToTyped(this);
      }
      if (an_other instanceof EquivalenceExpression) {
        return an_other.compareToTyped(this);
      } else {
        return BeetlzExpression.VERY_DIFF;
      }
    }

    /**
     * Does this expression contain an informal expression.
     * @see logic.BeetlzExpression#skip()
     * @return true if it is informal
     */
    @Override
    public boolean skip() {
      return my_expr.skip();
    }

    /**
     * Get Bon type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toBonStringSimple() {
      if (my_op == Operator.NOT) {
        return my_op.getBonName() + SPACE + my_expr.toBonString();
      }
      return my_op.getBonName() + my_expr.toBonString();
    }

    /**
     * Get Java type string.
     * @see logic.BeetlzExpression#toJavaString()
     * @return string representation
     */
    @Override
    public String toJavaStringSimple() {
      if (my_op == Operator.NOT) {
        return my_op.getJavaName() + SPACE + my_expr.toJavaString();
      }
      return my_op.getJavaName() + my_expr.toJavaString();
    }
  } //end Unary expr
} //end Expression


