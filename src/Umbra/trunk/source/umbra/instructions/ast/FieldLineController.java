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
 * This is a class for lines in bytecode files with the field declaration.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class FieldLineController extends BytecodeLineController {

  /**
   * This creates an instance of a bytecode line handle to handle
   * a line with a field declaration.
   *
   * @param a_line_text the string representation of the line text
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public FieldLineController(final String a_line_text) {
    super(a_line_text);
  }


  /**
   * This method checks the correctness of a field declaration line.
   *
   * @return  true if the line is correct
   */
  public boolean correct()  {
    boolean res = true;
    final InstructionParser parser = getParser();
    while (parser.swallowMnemonic(BytecodeStrings.FIELD_PREFIX) >= 0) {
      parser.swallowWhitespace();
    }
    res = res && parser.swallowArrType();
    res = res && parser.swallowWhitespace();
    res = res && parser.swallowFieldName();
    res = res && parser.swallowWhitespace();
    res = res && parser.swallowDelimiter(';');
    return res;
  }


  /**
   * This method checks if the particular line can be a field declaration
   * line.
   *
   * @param a_line the string to check if it can be a field declaration line
   * @return <code>true</code> when the string can be a field declaration line,
   *   <code>false</code> otherwise
   */
  public static boolean isFieldLineStart(final String a_line) {
    for (int i = 0; i < BytecodeStrings.FIELD_PREFIX.length; i++) {
      if (a_line.startsWith(BytecodeStrings.FIELD_PREFIX[i])) {
        return true;
      }
    }
    return false;
  }
}
