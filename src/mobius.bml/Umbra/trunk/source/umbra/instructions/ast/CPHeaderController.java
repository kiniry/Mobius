/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

import umbra.lib.BytecodeStrings;

/**
 * This is a class for lines in bytecode files with the constant pool header
 * information (i.e. "Constant pool:" or "Second constant pool:" constants.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class CPHeaderController extends BytecodeLineController {

  /**
   * This creates an instance of a bytecode line handle to handle
   * constant pool header.
   *
   * @param a_line_text the string representation of the line text
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public CPHeaderController(final String a_line_text) {
    super(a_line_text);
  }

  /**
   * This method checks the correctness of a class pool header line. In case of
   * the {@link CPHeaderController} this means that the line text starts with
   * the constant pool keyword (first or second one).
   *
   * @return  true if the instruction is correct
   */
  public boolean correct()  {
    return getLineContent().
             startsWith(BytecodeStrings.
                          JAVA_KEYWORDS[BytecodeStrings.CP_KEYWORD_POS]) ||
           getLineContent().
             startsWith(BytecodeStrings.
                          JAVA_KEYWORDS[BytecodeStrings.SCP_KEYWORD_POS]);
  }
}
