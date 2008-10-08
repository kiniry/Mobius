/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import umbra.instructions.InstructionParser;
import umbra.lib.BytecodeStrings;


/**
 * @author alx
 * @version a-01
 *
 */
public class CPLineController extends BytecodeLineController {

  private InstructionParser my_parser;
  private int my_constno;
  private int my_keyword;


  /**
   * This creates an instance of a bytecode line handle to handle
   * constant pool entry.
   *
   * @param a_line_text the string representation of the line text
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public CPLineController(final String a_line_text) {
    super(a_line_text);
  }


  /**
   * This method checks if the particular line can be a constant pool line.
   *
   * @param a_line the string to check if it can be a constant pool line
   * @return <code>true</code> when the string can be a constant pool line,
   *   <code>false</code> otherwise
   */
  public static boolean isCPLineStart(final String a_line) {
    return a_line.startsWith(BytecodeStrings.CP_ENTRY_PREFIX[0]);
  }


  /**
   * This method checks the correctness of a class pool line. In case of
   * the {@link CPLineController} this means that the line text starts with
   * the constant pool line keyword followed by a proper constant pool
   * entry.
   *
   * @return  true if the constant pool line is correct
   */
  public boolean correct()  {
    if (my_parser == null) {
      my_parser = new InstructionParser(getLineContent());
    }
    my_parser.resetParser();
    boolean res = true;
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowGivenWord(BytecodeStrings.JAVA_KEYWORDS[
                                 BytecodeStrings.CP_ENTRY_KEYWORD_POS]);
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter('#');
    res = res && my_parser.swallowNumber();
    if (res) {
      my_constno = my_parser.getResult();
    }
    res = res && my_parser.swallowWhitespace();
    res = res && my_parser.swallowDelimiter('=');
    return parseEntry(res);
  }


  /**
   * @param uptonow
   * @return
   */
  private boolean parseEntry(boolean utonow) {
    if (!utonow) {
      return utonow;
    }
    boolean res = utonow;
    res = res && my_parser.swallowWhitespace();
    my_keyword = my_parser.swallowMnemonic(BytecodeStrings.CP_TYPE_KEYWORDS);
    res = res && (my_keyword >= 0);
    return res;
  }
}
