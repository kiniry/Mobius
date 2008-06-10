/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
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
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class BytecodeStrings extends BytecodeStringsMnemonics {


  /**
   * This constant contains an array with all the BML keywords.
   * The BML lines are handled by
   * {@link umbra.instructions.ast.AnnotationLineController} class.
   *
   * FIXME: this should be retrieved from BMLlib;
   *   https://mobius.ucd.ie/ticket/551
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
   * This constant contains an array with all the possible prefixes of method
   * headers in byte code text files. The header lines are handled by
   * {@link umbra.instructions.ast.HeaderLineController} class.
   */
  public static final String[] HEADER_PREFIX = new String[] {"public",
                                                             "abstract",
                                                             "static", "void",
                                                             "private",
                                                             "int", "char",
                                                             "protected",
                                                             "boolean",
                                                             "String", "byte",
                                                             "package",
                                                             "class", "}" };

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
   * Private constructor added to prevent the creation of objects of this
   * type.
   */
  private BytecodeStrings() {
  }
}
