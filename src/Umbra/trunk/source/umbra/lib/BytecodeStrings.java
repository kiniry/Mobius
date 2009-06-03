/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;


/**
 * The container for all the byte code and BML strings. It inherits the
 * byte code mnemonics as well as strings indicating starts and ends of
 * comments and BML areas from {@link BytecodeStringsMnemonics}. It contributes
 * <ul>
 *  <li>BML keywords (e.g. requires),</li>
 *  <li>Java keywords (e.g. class, extends),</li>
 *  <li>BML expression kewords (e.g. \result),</li>
 *  <li>keywords for Line numbers section,</li>
 *  <li>keywords for Code section,</li>
 *  <li>keywords in method, classes, and package headers,</li>
 *  <li>keywords in throws section, and</li>
 *  <li>primitive types names.</li>
 * </ul>
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class BytecodeStrings extends BytecodeStringsMnemonics {


  /**
   * This constant contains an array with all the BML keywords.
   * The BML lines are handled by
   * {@link umbra.instructions.ast.AnnotationLineController} class.
   *
   */
  public static final String[] BML_KEYWORDS =
    annot.textio.DisplayStyle.BML_KEYWORDS;

  /**
   * This constant contains an array with all the Java keywords.
   * This array is based on the list in "The Java Language Specification,
   * Third Edition", Section 3.9 Keywords. See:
   * http://java.sun.com/docs/books/jls/third_edition/html/lexical.html#3.9
   */
  public static final String[] JAVA_KEYWORDS = new String[] {
    "abstract",
    "assert",
    "boolean",
    "break",
    "byte",
    "case",
    "catch",
    "char",
    "class",
    "const",
    "continue",
    "default",
    "do",
    "double",
    "else",
    "enum",
    "extends",
    "final",
    "finally",
    "float",
    "for",
    "if",
    "goto",
    "implements",
    "Constant pool:",
    "Second constant pool:",
    "instanceof",
    "int",
    "interface",
    "long",
    "native",
    "new",
    "package",
    "private",
    "protected",
    "public",
    "return",
    "short",
    "static",
    "strictfp",
    "super",
    "switch",
    "synchronized",
    "this",
    "throw",
    "throws",
    "transient",
    "try",
    "void",
    "volatile",
    "while"
  };

  /**
   * This constant contains an array with all the keywords for constant pool
   * areas. This array is based on the section "Textual Representation of
   * Specifications" of "BML Reference Manual"
   */
  public static final String[] CP_KEYWORDS = new String[] {
    "Class",
    "Fieldref",
    "Methodref",
    "InterfaceMethodref",
    "String",
    "Integer",
    "Float",
    "Long",
    "Double",
    "NameAndType",
    "Utf8",
    "const",
    "Constant pool:",
    "Second constant pool:"
  };

  /**
   * This constant contains an array with all the keywords for constant pool
   * types of entries. This array is based on the section "Textual
   * Representation of Specifications" of "BML Reference Manual"
   */
  public static final String[] CP_TYPE_KEYWORDS = new String[] {
    "Class",
    "Fieldref",
    "Methodref",
    "InterfaceMethodref",
    "String",
    "Integer",
    "Float",
    "Long",
    "Double",
    "NameAndType",
    "Utf8"
  };

  /**
   * The position of the "class" keyword in {@link #JAVA_KEYWORDS}.
   */
  public static final int CLASS_KEYWORD_POS = 8;

  /**
   * The position of the "const" keyword in {@link #JAVA_KEYWORDS}.
   */
  public static final int CP_ENTRY_KEYWORD_POS = 9;

  /**
   * The position of the "extends" keyword in {@link #JAVA_KEYWORDS}.
   */
  public static final int EXTENDS_KEYWORD_POS = 16;

  /**
   * The position of the "implements" keyword in {@link #JAVA_KEYWORDS}.
   */
  public static final int IMPLEMENTS_KEYWORD_POS = 23;

  /**
   * The position of the "Constant pool:" keyword in {@link #JAVA_KEYWORDS}.
   */
  public static final int CP_KEYWORD_POS = 24;

  /**
   * The position of the "Second constant pool:" keyword in
   * {@link #JAVA_KEYWORDS}.
   */
  public static final int SCP_KEYWORD_POS = 25;

  /**
   * This constant contains an array with all the keywords that occur in the
   * line numbers area. This area is not fully handled yet.
   *
   * FIXME: add the handling of this area; https://mobius.ucd.ie/ticket/547
   */
  public static final String[] LINE_KEYWORDS = new String[] {"Line", "numbers",
                                                             "Local",
                                                             "variable",
                                                             "table"};

  /**
   * This constant contains an array with all the keywords that occur in the
   * Code area. This area is not fully handled yet.
   *
   * FIXME: add the handling of this area; https://mobius.ucd.ie/ticket/548
   */
  public static final String[] CODE_KEYWORDS = new String[] {"Code",
                                                             "max_stack",
                                                             "max_locals",
                                                             "code_length"};

  /**
   * This constant contains an array with all the possible prefixes of field
   * declaration lines in byte code text files. The lines are handled by
   * {@link umbra.instructions.ast.FieldLineController} class.
   */
  public static final String[] FIELD_PREFIX = new String[] {"public",
                                                            "protected",
                                                            "private",
                                                            "static",
                                                            "abstract",
                                                            "final",
                                                            "strictfp",
                                                            "ghost",
                                                            "model",
                                                            "spec_public",
                                                            "spec_protected",
                                                            "non_null",
                                                            "nullable",
                                                            "pure",
                                                            "helper",
                                                            "peer",
                                                            "rep",
                                                            "readonly"};

  /**
   * This constant contains an index to the first BML field prefix in
   * {@link #FIELD_PREFIX} array.
   */
  public static final int BML_FIELD_PREFIX_START = 7;

  /**
   * This constant contains an index to the first BML access right in
   * {@link #FIELD_PREFIX} array.
   */
  public static final int BML_ACC_PREFIX_START = 9;


  /**
   * This constant contains an array with all the possible prefixes of method
   * headers in byte code text files. The header lines are handled by
   * {@link umbra.instructions.ast.HeaderLineController} class.
   */
  public static final String[] HEADER_PREFIX = new String[] {"package",
                                                             "class"};

  /**
   * This constant contains an array with all the possible prefixes of constant
   * pool lines in byte code text files. The constant pool lines are handled by
   * {@link umbra.instructions.ast.CPLineController} class.
   */
  public static final String[] CP_ENTRY_PREFIX = new String[] {" const #",
                                                               "const #"};

  /**
   * This constant contains an array with all the possible prefixes of throw
   * lines in byte code text files. The throw lines are handled by
   * {@link umbra.instructions.ast.ThrowsLineController} class.
   *
   * FIXME: add the handling of this area; https://mobius.ucd.ie/ticket/549
   */
  public static final String[] THROWS_PREFIX = new String[] {"throws",
                                                             "Exception",
                                                             "From"};

  /**
   * The names of base byte code types relevant for array instructions. These
   * are the primitive types.
   */
  public static final String[] PRIMITIVE_TYPE_NAMES = {"boolean", "char",
                                                       "float", "double",
                                                       "byte", "short",
                                                       "int", "long"};

  /**
   * The array which contains all the characters we consider here to be
   * whitespace characters.
   */
  public static final char[] WHITESPACE_CHARACTERS = {' ', '\t', '\n', '\r' };

  /**
   * The constant pool keyword for CONSTANT_Class_info entry.
   */
  public static final String CLASS_CP_ENTRY_KEYWORD = "Class";

  /**
   * The constant pool keyword for CONSTANT_Fieldref_info entry.
   */
  public static final String FIELDREF_CP_ENTRY_KEYWORD = "Fieldref";

  /**
   * The constant pool keyword for CONSTANT_Methodref_info entry.
   */
  public static final String METHODREF_CP_ENTRY_KEYWORD = "Methodref";

  /**
   * The constant pool keyword for CONSTANT_InterfaceMethodref_info entry.
   */
  public static final String INTERFACE_METHODREF_CP_ENTRY_KEYWORD =
    "InterfaceMethodref";

  /**
   * The constant pool keyword for CONSTANT_String_info entry.
   */
  public static final String STRING_CP_ENTRY_KEYWORD = "String";

  /**
   * The constant pool keyword for CONSTANT_Integer_info entry.
   */
  public static final String INTEGER_CP_ENTRY_KEYWORD = "Integer";

  /**
   * The constant pool keyword for CONSTANT_Float_info entry.
   */
  public static final String FLOAT_CP_ENTRY_KEYWORD = "Float";

  /**
   * The constant pool keyword for CONSTANT_Long_info entry.
   */
  public static final String LONG_CP_ENTRY_KEYWORD = "Long";

  /**
   * The constant pool keyword for CONSTANT_Double_info entry.
   */
  public static final String DOUBLE_CP_ENTRY_KEYWORD = "Double";

  /**
   * The constant pool keyword for CONSTANT_NameAndType_info entry.
   */
  public static final String NAME_AND_TYPE_CP_ENTRY_KEYWORD = "NameAndType";

  /**
   * The constant pool keyword for CONSTANT_Utf8_info entry.
   */
  public static final String UTF8_CP_ENTRY_KEYWORD = "Utf8";

  /**
   * Private constructor added to prevent the creation of objects of this
   * type.
   */
  private BytecodeStrings() {
  }
}
