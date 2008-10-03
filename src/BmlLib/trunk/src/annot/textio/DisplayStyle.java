package annot.textio;

/**
 * This interface describes how BML annotations should be
 * displayed.
 *
 * It also contains the information on the BML attribute names which are stored
 * in primary constantPool).
 *
 * Note: be careful to modify BML.g3 as well
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class DisplayStyle {

  /**
   * The common prefix of all the BML attribute names.
   */
  public static final String BML_DOMAIN = "org.bmlspecs.";

  /**
   * The String with the name of the Version attribute.
   */
  public static final String VERSION_ATTR = BML_DOMAIN + "Version";

  /**
   * The String with the name of the ClassModifiers attribute.
   */
  public static final String CLASS_MODIFIERS_ATTR = BML_DOMAIN +
    "ClassModifiers";

  /**
   * The String with the name of the GhostFields attribute.
   */
  public static final String GHOST_FIELDS_ATTR = BML_DOMAIN +
    "GhostFields";

  /**
   * The String with the name of the ModelFields attribute.
   */
  public static final String MODEL_FIELDS_ATTR = BML_DOMAIN +
    "ModelFields";

  /**
   * The String with the name of the ModelMethods attribute.
   */
  public static final String MODEL_METHODS_ATTR = BML_DOMAIN +
    "ModelMethods";

  /**
   * The String with the name of the Invariants attribute.
   */
  public static final String INVARIANTS_ATTR = BML_DOMAIN + "Invariants";

  /**
   * The String with the name of the Constraints attribute.
   */
  public static final String CONSTRAINTS_ATTR = BML_DOMAIN + "Constraints";

  /**
   * The String with the name of the InitiallyClauses attribute.
   */
  public static final String INITIALLY_CLAUSES_ATTR = BML_DOMAIN +
    "InitiallyClauses";

  /**
   * The String with the name of the RepresentsClauses attribute.
   */
  public static final String REPRESENTS_CLAUSES_ATTR = BML_DOMAIN +
    "RepresentsClauses";

  /**
   * The String with the name of the SecondConstantPool attribute.
   */
  public static final String SECOND_CONSTANT_POOL_ATTR = BML_DOMAIN +
    "SecondConstantPool";

  /**
   * The String with the name of the DataGroups attribute.
   */
  public static final String DATA_GROUPS_ATTR = BML_DOMAIN +
    "DataGroups";

  /**
   * The String with the name of the FieldModifiers attribute.
   */
  public static final String FIELD_MODIFIERS_ATTR = BML_DOMAIN +
    "FieldModifiers";

  /**
   * The String with the name of the MethodSpecification attribute.
   */
  public static final String METHOD_SPECIFICATION_ATTR = BML_DOMAIN +
    "MethodSpecification";

  /**
   * The String with the name of the ParameterTable attribute.
   */
  public static final String PARAMETER_TABLE_ATTR = BML_DOMAIN +
    "ParameterTable";

  /**
   * The String with the name of the LocalVariableModifiersTable attribute.
   */
  public static final String LOCAL_VARIABLE_MODIFIERS_TABLE_ATTR = BML_DOMAIN +
    "LocalVariableModifiersTable";

  /**
   * The String with the name of the LocalGhostVariableTable attribute.
   */
  public static final String LOCAL_GHOST_VARIABLE_TABLE_ATTR = BML_DOMAIN +
    "LocalGhostVariableTable";

  /**
   * The String with the name of the AssertTable attribute.
   */
  public static final String ASSERT_TABLE_ATTR = BML_DOMAIN + "AssertTable";

  /**
   * The String with the name of the AssumeTable attribute.
   */
  public static final String ASSUME_TABLE_ATTR = BML_DOMAIN + "AssumeTable";

  /**
   * The String with the name of the SetTable attribute.
   */
  public static final String SET_TABLE_ATTR = BML_DOMAIN + "SetTable";

  /**
   * The String with the name of the UnreachableTable attribute.
   */
  public static final String UNREACHABLE_TABLE_ATTR = BML_DOMAIN +
    "UnreachableTable";

  /**
   * The String with the name of the LoopSpecificationTable attribute.
   */
  public static final String LOOP_SPECIFICATION_TABLE = BML_DOMAIN +
    "LoopSpecificationTable";

  /**
   * The String with the name of the OwnershipTable attribute.
   */
  public static final String OWNERSHIP_TABLE = BML_DOMAIN +
    "OwnershipTable";

  /**
   * The String with the name of the DebugTable attribute.
   */
  public static final String DEBUG_TABLE = BML_DOMAIN +
    "DebugTable";

  /**
   * Java keyword for package.
   */
  public static final String PACKAGE_KWD = "package";

  /**
   * BML keyword for default package name.
   */
  public static final String DEFAULT_PACKAGE_NAME_KWD = "[default]";

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

  public static final String _assert = "assert";

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
   * The @ sign to be used as BML comment indicator
   */
  public static final String BML_AT_SIGN = "@";

  /**
   * The string which starts a BML area.
   * @see COMMENT_LENGTH
   */
  public static final String BML_COMMENT_START = "/*" + BML_AT_SIGN + " ";

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

  /**
   * A private constructor to forbid the creation of instances.
   */
  protected DisplayStyle() {
  }
}
