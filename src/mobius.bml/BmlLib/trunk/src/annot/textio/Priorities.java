package annot.textio;

import annot.io.Code;

/**
 * This class contains priorities of all expression types.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class Priorities extends Code {

  /**
   * The same priority as in it's parent, so it will never
   * be surrounded by ( ).
   */
  public static final int PRI_TRANSPARENT = -2;

  /**
   * Priority of operands that have no subexpressions.
   */
  public static final int LEAF = 0;

  /**
   * Priority of array and field access operators.
   */
  public static final int ACCESS_PRIORITY = 1;

  /**
   * Priority of one parameter negation operators.
   */
  public static final int NEGATION_PRIORITY = 3;

  /**
   * Priority of multiplicative operators.
   */
  public static final int MULTIPLICATIVE_PRIORITY = 4;

  /**
   * Priority of additive operators.
   */
  public static final int ADDITIVE_PRIORITY = 5;

  /**
   * Priority of bit shift operators.
   */
  public static final int SHIFTOP_PRIORITY = 6;

  /**
   * Priority of ordering relations.
   */
  public static final int ORDER_PRIORITY = 7;

  /**
   * Priority of equality relations.
   */
  public static final int EQUALITY_PRIORITY = 8;

  /**
   * Priority of bitwise NOT operators.
   */
  public static final int BITWISENOT_PRIORITY = 9;

  /**
   * Priority of bitwise AND operators.
   */
  public static final int BITWISEAND_PRIORITY = 10;

  /**
   * Priority of bitwise XOR operators.
   */
  public static final int BITWISEXOR_PRIORITY = 11;

  /**
   * Priority of bitwise OR operators.
   */
  public static final int BITWISEOR_PRIORITY = 12;

  /**
   * Priority of logical conjunction operators.
   */
  public static final int LOGICALAND_PRIORITY = 13;

  /**
   * Priority of logical alternative operators.
   */
  public static final int LOGICALOR_PRIORITY = 14;

  /**
   * Priority of logical implication operators.
   */
  public static final int LOGICALIMPL_PRIORITY = 15;

  /**
   * Priority of logical equivalence operators.
   */
  public static final int LOGICALEQUIV_PRIORITY = 16;

  /**
   * Priority of the conditional expression.
   */
  public static final int COND_PRIORITY = 17;

  /**
   * Priority of quantifiers.
   */
  public static final int QUANTIFIER_PRIORITY = 18;

  /**
   * Maximum possible expression priority.
   */
  public static final int MAX_PRI = 18;

  /**
   * The associativity value which indicates no associativity at all.
   */
  public static final int ANONE = 0;

  /**
   * The associativity value which indicates the associativity to the left.
   */
  public static final int ALEFT = 1;

  /**
   * The associativity value which indicates associatibity to the right.
   */
  public static final int ARIGHT = 2;

  /**
   * The associativity value which indicates the associativity both to the left
   * and to the right.
   */
  public static final int ABOTH = 3;

  /**
   * The total maximal number of operators for which the associativity and
   * priority are defined.
   */
  public static final int NUMBER_OF_OPERATORS = 256;

  /**
   * Whether binary operators are associative
   * (ANONE, ALEFT, ARIGHT or ABOTH, for non-associative,
   * left-, right- and both-associative opcodes).
   */
  private static int[] associative;

  /**
   * Expression's priority array, from expression's type
   * (connector, from {@link Code} interface) to it's
   * priority.
   */
  private static int[] priorities;

  /**
   * An empty private constructor to disallow the creation of instances.
   */
  private Priorities() {
  }

  /**
   * Returns priority of expression with given type
   * (connector). Sets all priorities at first call.
   *
   * @param opcode - expression type (connector), from
   *     {@link Code} interface.
   * @return Priority of operators of given type.
   */
  public static int getPriority(final int opcode) {
    if (priorities == null) {
      setPriorities();
    }
    if (opcode  >  NUMBER_OF_OPERATORS) {
      throw new RuntimeException("invalid opcode: " + opcode);
    }
    if (priorities[opcode] == -1) {
      throw new RuntimeException("invalid opcode: " + opcode);
    }
    return priorities[opcode];
  }

  /**
   * Checks whether given operator is associative.
   *
   * @param opcode - operator opcode,
   * @param dir - associavity direction (ANONE, ALEFT,
   *         ARIGHT or ABOTH, for non-associative,
   *         left-, right- and both-associative
   *         opcodes)
   * @return true for binary operators op that are assotiative
   *         in (at least) given direction.
   */
  public static boolean isAssociative(final int opcode, final int dir) {
    if (associative == null) {
      setAssociativity();
    }
    if (opcode  >  NUMBER_OF_OPERATORS) {
      throw new RuntimeException("invalid opcode: " + opcode);
    }
    return (associative[opcode] & dir)  >  0;
  }

  /**
   * Initializes the associativity of operators.
   */
  private static void setAssociativity() {
    associative = new int[NUMBER_OF_OPERATORS];
    for (int i = 0; i  <  NUMBER_OF_OPERATORS; i++) {
      associative[i] = ALEFT;
    }
    associative[MULT] = ABOTH;
    associative[PLUS] = ABOTH;
    associative[AND] = ABOTH;
    associative[OR] = ABOTH;
    associative[BITWISEAND] = ABOTH;
    associative[BITWISEOR] = ABOTH;
    associative[BITWISEXOR] = ABOTH;
    associative[EQ] = ABOTH;
    associative[NOTEQ] = ABOTH;
    associative[EQUIV] = ABOTH;
    associative[NOTEQUIV] = ABOTH;
    associative[COND_EXPR] = ABOTH;
    associative[IMPLIES] = ARIGHT;
  }

  /**
   * Initializes the priorities of operators.
   */
  private static void setPriorities() {
    priorities = new int[NUMBER_OF_OPERATORS];
    for (int i = 0; i  <  NUMBER_OF_OPERATORS; i++) {
      priorities[i] = LEAF;
    }
    priorities[ARRAY_ACCESS] = ACCESS_PRIORITY;
    priorities[FIELD_ACCESS] = ACCESS_PRIORITY;
    priorities[NOT] = NEGATION_PRIORITY;
    priorities[NEG] = NEGATION_PRIORITY;
    setPrioritiesArith();
    priorities[SHL] = SHIFTOP_PRIORITY;
    priorities[SHR] = SHIFTOP_PRIORITY;
    priorities[USHR] = SHIFTOP_PRIORITY;
    setPrioritiesComparisons();
    priorities[BITWISENOT] = BITWISENOT_PRIORITY;
    priorities[BITWISEAND] = BITWISEAND_PRIORITY;
    priorities[BITWISEXOR] = BITWISEXOR_PRIORITY;
    priorities[BITWISEOR] = BITWISEOR_PRIORITY;
    setPrioritiesLogical();
    priorities[COND_EXPR] = COND_PRIORITY;
    // ?
    setPrioritiesQuantifiers();
  }

  /**
   * Initializes the priorities of the comparison operators.
   */
  private static void setPrioritiesComparisons() {
    priorities[LESS] = ORDER_PRIORITY;
    priorities[LESSEQ] = ORDER_PRIORITY;
    priorities[GRT] = ORDER_PRIORITY;
    priorities[GRTEQ] = ORDER_PRIORITY;
    priorities[EQ] = EQUALITY_PRIORITY;
    priorities[NOTEQ] = EQUALITY_PRIORITY;
  }

  /**
   * Initializes the priorities of the arithmetical operators.
   */
  private static void setPrioritiesArith() {
    priorities[MULT] = MULTIPLICATIVE_PRIORITY;
    priorities[DIV] = MULTIPLICATIVE_PRIORITY;
    priorities[REM] = MULTIPLICATIVE_PRIORITY;
    priorities[PLUS] = ADDITIVE_PRIORITY;
    priorities[MINUS] = ADDITIVE_PRIORITY;
  }

  /**
   * Initializes the priorities of the logical operators.
   */
  private static void setPrioritiesLogical() {
    priorities[AND] = LOGICALAND_PRIORITY;
    priorities[OR] = LOGICALOR_PRIORITY;
    priorities[IMPLIES] = LOGICALIMPL_PRIORITY;
    priorities[EQUIV] = LOGICALEQUIV_PRIORITY;
    priorities[NOTEQUIV] = LOGICALEQUIV_PRIORITY;
  }

  /**
   * Initializes the priorities of the quantification operators.
   */
  private static void setPrioritiesQuantifiers() {
    priorities[FORALL] = QUANTIFIER_PRIORITY;
    priorities[EXISTS] = QUANTIFIER_PRIORITY;
    priorities[FORALL_WITH_NAME] = QUANTIFIER_PRIORITY;
    priorities[EXISTS_WITH_NAME] = QUANTIFIER_PRIORITY;
  }

}
