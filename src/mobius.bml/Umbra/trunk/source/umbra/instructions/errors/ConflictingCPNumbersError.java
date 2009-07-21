/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.errors;

import umbra.instructions.ast.BytecodeLineController;
import umbra.instructions.ast.CPLineController;

/**
 * This class represents an error of two or more constant pool entries
 * having the same constant number.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ConflictingCPNumbersError extends BytecodeError {

  /**
   * The constant number of the conflicting CP entries.
   */
  private int my_number;

  /**
   * Returns the constant number of the conflicting CP entries.
   *
   * @return the constant number
   */
  public int getNumber() {
    return my_number;
  }

  /**
   * Adds a line to the list of lines in which an error occured and
   * extracts a constant number from it. All the lines should be
   * CPLineControllers with the same constant number.
   *
   * @param a_line a line to be added
   */
  public void addLine(final BytecodeLineController a_line) {
    final CPLineController cplc = (CPLineController) a_line;
    my_number = cplc.getConstantNumber();
    super.addLine(a_line);
  }

  /**
   * Returns textual representation of the error.
   *
   * @return a string with error message
   */
  public String getShortErrorMessage() {
    return "Conflicting numbers of constant pool entries, number #" +
      my_number + " used more than once";
  }

  /**
   * Returns textual representation of the error intended to
   * be used with line contents. I.e.: <br> <br>
   *
   * Conflicting numbers of constant pool entries: <br>
   * const #1 = Utf8 "cat"; <br>
   * const #1 = Utf8 "dog"; <br>
   *
   * @return a string with error message
   */
  public String getErrorMessage() {
    return "Conflicting numbers of constant pool entries:";
  }


}
