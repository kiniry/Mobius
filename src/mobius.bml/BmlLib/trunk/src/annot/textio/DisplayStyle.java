package annot.textio;

/**
 * This class describes how BML annotations should be
 * displayed.
 *
 * Be careful to modify BML.g3 as well
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class DisplayStyle {

  /**
   * This constant contains an array with all the BML keywords.
   * The BML lines are handled by
   * {@link umbra.instructions.ast.AnnotationLineController} class.
   */
  public static final String[] BML_KEYWORDS = new String[] {
    "invariant",
    "assert",
    "requires",
    "{|",
    "|}",
    "precondition",
    "modifies",
    "ensures",
    "exsures",
    "\\result",
    "loop_specification",
    "modifies",
    "loop_inv",
    "decreases"};

  /**
   * Java keyword for package.
   */
  public static final String PACKAGE_KWD = "package";

  /**
   * Java keyword for static.
   */
  public static final String STATIC_KWD = "static";

  /**
   * BML keyword for default package name.
   */
  public static final String DEFAULT_PACKAGE_NAME_KWD = "[default]";

  /**
   * BML "invariant" keyword.
   */
  public static final String INVARIANT_KWD = "invariant";

  /**
   * BML keyword for the constant pool header.
   */
  public static final String CONSTANT_POOL_KWD = "Constant pool:";

  /**
   * BML keyword for the second constant pool header.
   */
  public static final String SECOND_CONSTANT_POOL_KWD = "Second constant pool:";

  /**
   * BML keyword for const in the constant pool.
   */
  public static final String CONST_KWD = "const";

  /**
   * BML keyword for "Class" type in the constant pool.
   */
  public static final String CLASS_KWD = "Class";

  /**
   * BML keyword for "Fieldref" type in the constant pool.
   */
  public static final String FIELDREF_KWD = "Fieldref";

  /**
   * BML keyword for "Methodref" type in the constant pool.
   */
  public static final String METHODREF_KWD = "Methodref";

  /**
   * BML keyword for "InterfaceMethodref" type in the constant pool.
   */
  public static final String INTERFACEMETHODREF_KWD = "InterfaceMethodref";

  /**
   * BML keyword for "String" type in the constant pool.
   */
  public static final String STRING_KWD = "String";

  /**
   * BML keyword for "Integer" type in the constant pool.
   */
  public static final String INTEGER_KWD = "Integer";

  /**
   * BML keyword for "Float" type in the constant pool.
   */
  public static final String FLOAT_KWD = "Float";

  /**
   * BML keyword for "Long" type in the constant pool.
   */
  public static final String LONG_KWD = "Long";

  /**
   * BML keyword for "Double" type in the constant pool.
   */
  public static final String DOUBLE_KWD = "Double";

  /**
   * BML keyword for "NameAndType" type in the constant pool.
   */
  public static final String NAMEANDTYPE_KWD = "NameAndType";

  /**
   * BML keyword for "Utf8" type in the constant pool.
   */
  public static final String UTF8_KWD = "Utf8";
  /**
   * BML loop "decreases" keyword.
   */
  public static final String DECREASES_KWD = "decreases";

  /**
   * BML loop invariant ("loop_inv") keyword.
   */
  public static final String LOOP_INV_KWD = "loop_inv";

  /**
   * BML loop specification ("loop_specification") keyword.
   */
  public static final String LOOPSPEC_KWD = "loop_specification";

  /**
   * BML "requires" keyword.
   */
  public static final String REQUIRES_KWD = "requires";

  /**
   * BML "modifies" keyword.
   */
  public static final String MODIFIES_KWD = "modifies";

  /**
   * BML "ensures" keyword.
   */
  public static final String ENSURES_KWD = "ensures";

  /**
   * BML "signals" keyword.
   */
  public static final String SIGNALS_KWD = "signals";

  /**
   * BML "signals_only" keyword.
   */
  public static final String SIGNALS_ONLY_KWD = "signals_only";

  /**
   * BML "\nothing" keyword.
   */
  public static final String NOTHING_KWD = "\\nothing";

  /**
   * BML "\result" keyword.
   */
  public static final String RESULT_KWD = "\\result";

  /**
   * BML "\length" keyword.
   */
  public static final String LENGTH_KWD = "\\length";

  /**
   * BML "\old" keyword.
   */
  public static final String OLD_KWD = "\\old";

  /**
   * BML "\type" keyword.
   */
  public static final String TYPE_SMALL_KWD = "\\type";

  /**
   * BML "\TYPE" keyword.
   */
  public static final String TYPE_KWD = "\\TYPE";

  /**
   * BML "\nonnullelements" keyword.
   */
  public static final String NONNULLELEMENTS_KWD = "\\nonnullelements";

  /**
   * BML "assert" keyword.
   */
  public static final String ASSERT_KWD = "assert";

  /**
   * BML keyword for "spec_public" modifier.
   */
  public static final String SPEC_PUBLIC_KWD = "spec_public";

  /**
   * BML keyword for "spec_protected" modifier.
   */
  public static final String SPEC_PROTECTED_KWD = "spec_protected";

  /**
   * BML keyword for "non_null" modifier.
   */
  public static final String NON_NULL_KWD = "non_null";


  /**
   * BML keyword for "nullable" modifier.
   */
  public static final String NULLABLE_KWD = "nullable";


  /**
   * BML keyword for "pure" modifier.
   */
  public static final String PURE_KWD = "pure";


  /**
   * BML keyword for "helper" modifier.
   */
  public static final String HELPER_KWD = "helper";


  /**
   * BML keyword for "peer" modifier.
   */
  public static final String PEER_KWD = "peer";


  /**
   * BML keyword for "rep" modifier.
   */
  public static final String REP_KWD = "rep";


  /**
   * BML keyword for "readonly" modifier.
   */
  public static final String READONLY_KWD = "readonly";

  /**
   * Java keyword for "null" value.
   */
  public static final String NULL_KWD = "null";

  /**
   * Java keyword for "this" identifier.
   */
  public static final String THIS_KWD = "this";

  /**
   * BML keyword for "ghost" modifier.
   */
  public static final String GHOST_KWD = "ghost";

  /**
   * BML keyword for "model" modifier.
   */
  public static final String MODEL_KWD = "model";

  /**
   * Array with all the BML modifiers.
   */
  public static final String[] BML_MODIFIERS = {
    SPEC_PUBLIC_KWD,
    SPEC_PROTECTED_KWD,
    NON_NULL_KWD,
    NULLABLE_KWD,
    PURE_KWD,
    HELPER_KWD,
    PEER_KWD,
    REP_KWD,
    READONLY_KWD
  };

  /**
   * The hash sign to be used in numbers of constants.
   */
  public static final String HASH_SIGN = "#";

  /**
   * The = sign to be used in numbers of constants.
   */
  public static final String EQUALS_SIGN = "=";

  /**
   * The : sign to be used in numbers of constants.
   */
  public static final String COLON_SIGN = ":";

  /**
   * The ; sign to be used in numbers of constants.
   */
  public static final String SEMICOLON_SIGN = ";";

  /**
   * The . sign to be used in numbers of constants.
   */
  public static final String DOT_SIGN = ".";

  /**
   * The @ sign to be used as BML comment indicator.
   */
  public static final String BML_AT_SIGN = "@";

  /**
   * The string which starts a BML area.
   * @see COMMENT_LENGTH
   */
  public static final String BML_COMMENT_START = "/*" + BML_AT_SIGN;

  /**
   * The string which ends a BML area.
   */
  public static final String BML_COMMENT_END = BML_AT_SIGN + "*/";

  /**
   * The string which ends a BML area together with initial spaces.
   * @see COMMENT_LENGTH
   */
  public static final String BML_COMMENT_END_WITH_SPACES = "  " +
    BML_COMMENT_END;

  /**
   * The string which starts internal lines of multi-line BML comments.
   * @see COMMENT_LENGTH
   */
  public static final String BML_COMMENT_NEXT = "  " + BML_AT_SIGN + " ";

  /**
   * The length of BML_COMMENT_START, BML_COMMENT_END_WITH_SPACES, and
   * BML_COMMENT_NEXT. All should have the same length.
   */
  public static final int COMMENT_LENGTH = BML_COMMENT_NEXT.length(); //careful

  /**
   * The string which starts one line BML comments.
   */
  public static final String ONE_LINE_BML_START = "//@";

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
  public static final boolean DISPLAY_3ARG_QUANTIFIERS = true;

  /**
   * Debug mode (displays AST below each annotation).
   */
  public static final boolean DEBUG_CONTROL_PRINT = false;

  /**
   * Shows right margin in displayed code, after
   * {@value #MAX_TOTAL_LINE_WIDTH}'s character,
   * for prettyPrinter debugging only. Some features such as
   * CodeSearch mechanisms may not work with this flag on.
   */
  public static final boolean DISPLAY_RIGHT_MARGIN_MARKS = false;

  /**
   * Indicates if a simplified (raw) prettyPrinter should be used or not.
   * Set in to <code>true</code> only if main (advanced) prettyPrinter
   * makes several errors and resulting code is unreadable.
   */
  public static final boolean DISPLAY_USE_SIMPLE_PRETTYPRINTER = false;

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

  /**
   * A private constructor to forbid the creation of instances.
   */
  protected DisplayStyle() {
  }

}
