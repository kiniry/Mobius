package annot.textio;

/**
 * This interface describes how BML annotations should be
 * displayed.
 *
 * Note: be careful to modify BML.g3 as well
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class DisplayStyle {

  public static final String __assertTable = "Assert";

  public static final String __classInvariant = "ClassInvariant";

  public static final String __loopSpecTable = "LoopSpecification";

  /**
   * BML attribute names (stored in primary constantPool).
   */
  public static final String __mspec = "MethodSpecification";

  public static final String __second_cp = "SecondConstantPool";

  public static final String _assert = "assert";

  /**
   * BML annotations keywords (at the beginning
   * of annotations only). If you want to change them,
   * remember to update lexer (in BML.g3).
   * Must not end with whitespace (it causes errors
   * in tests)!
   *
   * Be careful to modify BML.g3 as well
   */
  public static final String _classInvariant = "invariant";

  public static final String _exsures = "exsures";

  public static final String _loop_decreases = "decreases";

  public static final String _loop_invariant = "loop_inv";

  public static final String _loop_modifies = "modifies";

  public static final String _loopspec = "loop_specification";

  public static final String _modifies = "modifies";

  public static final String _postcondition = "ensures";

  public static final String _precondition = "precondition";

  public static final String _requires = "requires";

  public static final String _result = "\\result";

  public static final String _sc_end = "|}";

  public static final String _sc_start = "{|";

  public static final String _staticInvariant = "static invariant";

  public static final String comment_end = "  @*/"; //careful

  public static final String COMMENT_NEXT = "  @ ";

  /**
   * length of comment marks above.
   */
  public static final int COMMENT_LENGTH = COMMENT_NEXT.length();


  /**
   * Beginning, next line, and end of BML annotation comment.
   * All should have the same length:
   */
  public static final String comment_start = "/*@ "; //careful

  /**
   * Character which marks the start of a block expression.
   */
  public static final char BLOCK_EXPR_START = '{';

  /**
   * Character which marks the end of a block expression.
   */
  public static final char BLOCK_EXPR_END = '}';

  /**
   * whether display each implication branch of quantified
   * formula at the same level as quantifier itself or not.
   */
  public static final boolean go3argQuantifiers = true;

  /**
   * Debug mode (displays AST below each annotation).
   */
  public static final boolean goControlPrint = false;

  /**
   * Shows right margin in displayed code, after
   * {@value #MAX_TOTAL_LINE_WIDTH}'s character,
   * for prettyPrinter debugging only. Some features like
   * CodeSearch mechanisms may not work with this flag on.
   */
  public static final boolean goShowRightMargin = false;

  /**
   * whether use simplified (raw) prettyPrinter or not.
   * Set in to true only if main (advanced) prettyPrinter
   * makes several errors and resulting code became
   * unreadable.
   */
  public static final boolean goUseSimplePrettyPrinter = false;

  /**
   * The string with name of integer boolean type.
   */
  public static final String JT_BOOLEAN = "boolean";

  /**
   * The string with name of integer int type.
   */
  public static final String JT_INT = "int";

  /**
   * Line indentation increment.
   */
  public static final String LINE_INDENT_STRING = "  ";

  /**
   * Maximum line width, for line-breaking.
   */
  public static final int MAX_TOTAL_LINE_WIDTH = 76;

}
