/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.ast;

/**
 * This class handles the incorrect constant pool entry. By incorrect
 * constant pool entry we understand a line that does not starts with
 * "[]*const[]*#&lt;positive integer&gt;[]*=[]*{constant pool entry keyword}"
 * and is parsed by Preparsing class in constant pool context.
 * This class is currently unused.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class IncorrectCPLineController extends CPLineController {

  /**
   * This creates an instance of a bytecode line handle to handle
   * incorrect constant pool entry.
   *
   * @param a_line_text the string representation of the line text
   * @param an_entry_type the string "", ignored parameter
   * for compatibility with
   * {@link umbra.instructions.DispatchingAutomaton#callConstructor}
   * @see BytecodeLineController#BytecodeLineController(String)
   */
  public IncorrectCPLineController(final String a_line_text,
                                   final String an_entry_type) {
    super(a_line_text, an_entry_type);
  }

  /**
   * This method returns the string "" which describes
   * incorrect constant pool entry handled by the current class.
   *
   * @return handled entry type
   */
  public static String getEntryType() {
    return "";
  }

  /**
   * This method always return false as this class handles incorrect
   * lines.
   *
   * @return always false
   */
  public boolean correct() {
    return false;
  }

}
