/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;


/**
 * String arrays used to identify keywords and instruction
 * names in byte code.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Jarosław Paszek (jp209217@students.mimuw.edu.pl)
 * @version a-01
 */
public final class BytecodeStrings extends BytecodeStringsMnemonics {


  /**
   * TODO.
   */
  public static final String[] BML_KEYWORDS = new String[] {"requires",
                                                            "ensures",
                                                            "exsures" };

  /**
   * TODO.
   */
  public static final String[] JAVA_KEYWORDS = new String[] {"public",
                                                             "protected",
                                                             "private",
                                                             "static", "void",
                                                             "int", "long",
                                                             "short", "char",
                                                             "byte", "boolean",
                                                             "class",
                                                             "interface",
                                                             "extends",
                                                             "implements",
                                                             "package"};

  /**
   * TODO.
   */
  public static final String[] LINENUM_KEYWORDS =
                                      new String[] {"Line numbers:",
                                                    "Local variable table:" };

  /**
   * TODO.
   */
  public static final String[] LINE_KEYWORDS = new String[] {"Line", "numbers",
                                                             "Local",
                                                             "variable",
                                                             "table"};

  /**
   * TODO.
   */
  public static final String[] CODE_KEYWORDS = new String[] {"Code",
                                                             "max_stack",
                                                             "max_locals",
                                                             "code_length"};

  /**
   * TODO.
   */
  public static final char[] KEY_TYPE_CHARS = new char[] {'B', 'C', 'D', 'I',
                                                          'S', 'V'};

  /**
   * This constant contains an array with all the possible prefixes of method
   * headers in byte code text files. The header lines are handled by
   * {@ref HeaderLineController} class.
   */
  public static final String[] HEADER_PREFIX = new String[] {"public",
                                                             "static", "void",
                                                             "private",
                                                             "int", "char",
                                                             "protected",
                                                             "boolean",
                                                             "String", "byte",
                                                             "package",
                                                             "class", "}" };
  /**
   * The names of base byte code types relevant for array instructions. These
   * are the primitive types.
   */
  public static final String[] PRIMITIVE_TYPE_NAMES = {"boolean", "char",
                                                       "float", "double",
                                                       "byte", "short",
                                                       "int", "long"};


  /**
   * Private constructor added to prevent the creation of objects of this
   * type.
   */
  private BytecodeStrings() {
  }
}
