/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import umbra.lib.BytecodeStrings;

/**
 * This class is used to parse fragments of byte code textual documents
 * which contain a class header.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class ClassHeaderParser extends InstructionNameParser {

  /**
   * This constructor sets the string to be parsed and resets the parser
   * so that it is ready to analyse the content. It relies on the
   * work in the superclass.
   *
   * @param a_line the line with the content to parse
   */
  public ClassHeaderParser(final String a_line) {
    super(a_line);
  }

  /**
   * This method swallows the "class" keyword. In case the "class" keyword
   * is swallowed it forwards the parser pointer to point to the first
   * character after the keyword. In case the keyword is not swallowed
   * it does not move the pointer.
   *
   * @return <code>true</code> if the "class" keyword was swallowed
   *   successfully, <code>false</code> otherwise.
   */
  public boolean swallowClass() {
    final String clstr =
      BytecodeStrings.JAVA_KEYWORDS[BytecodeStrings.CLASS_KEYWORD_POS];
    return swallowGivenWord(clstr);
  }


  /**
   * Swallows the extends clause. This routine follows
   * the definition from the BML Reference Manual. The format of the line
   * follows the following grammar:
   *     extends name
   * We assume there is no whitespace at the beginning of the parsed
   * text.
   *
   * @return <code>true</code> in case the extends clause is swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowExtendsClause() {
    final String clstr =
      BytecodeStrings.JAVA_KEYWORDS[BytecodeStrings.EXTENDS_KEYWORD_POS];
    boolean res = swallowGivenWord(clstr);
    res = res && swallowWhitespace();
    return res && swallowClassname();
  }

  /**
   * Swallows the implements clause. This routine follows
   * the definition from the BML Reference Manual. The format of the string
   * follows the following grammar:
   *    implements name-list
   * where name-list is
   *    name [, name ]..
   *
   * @return <code>true</code> in case the implements clause is swallowed,
   *   <code>false</code> otherwise
   */
  public boolean swallowImplementsClause() {
    final String clstr =
      BytecodeStrings.JAVA_KEYWORDS[BytecodeStrings.IMPLEMENTS_KEYWORD_POS];
    boolean res = swallowGivenWord(clstr);
    do {
      res = res && swallowWhitespace();
      res = res && swallowClassname();
      swallowWhitespace();
    } while (swallowDelimiter(','));
    return res;
  }
}
