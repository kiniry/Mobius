/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

import umbra.editor.parsing.BytecodeStrings;


/**
 * This is a class for lines in bytecode files that occur at the beginning
 * of methods. These are intended not to be edited by a user.
 *
 * @author Tomek Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class HeaderLineController extends BytecodeLineController {

  /**
   * This creates an instance of a bytecode line handle
   * which occurs at the beginning of a method 
   * <code>a_line</code>. Currently it just calls the constructor of the
   * superclass.
   *
   * @param a_line_text the string representation of the line text
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public HeaderLineController(final String a_line_text) {
    super(a_line_text);
  }

  /**
   * Checks the correctness of the current header line. This method checks only
   * the approximate format. It checks if the header line starts with one of
   * the fixed prefixes. The prefixes are enumerated in
   * {@ref BytecodeStrings#HEADER_PREFIX}.
   *
   * @return <code>true</code> when the line starts with a header prefix,
   *   <code>false</code> otherwise
   */
  public final boolean correct() {
    String[] prefs = BytecodeStrings.HEADER_PREFIX;
    String line = getMy_line_text();
    for (int i = 0; i < prefs.length; i++)
      if (line.startsWith(prefs[i])) return true;
    return false;
  }

  /**
   * This method sets the number of the method which the current line belongs
   * to. The method index of the header is equal to the number of the previous
   * line increased by one. This code allows to change the method number with
   * each method.
   *
   * @param an_index method number of the previous method
   */
  public final void setIndex(final int an_index) {
    super.setIndex(an_index + 1);
  }
}
