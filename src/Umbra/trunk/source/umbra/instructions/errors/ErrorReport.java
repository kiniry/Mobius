/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.errors;

import java.util.ArrayList;

/**
 * This class is used for reporting malformed parts of textual
 * bytecode representation.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ErrorReport {

  /**
   * List of errors.
   */
  private ArrayList < BytecodeError > my_errors;

  /**
   * Default constructor.
   */
  public ErrorReport() {
    my_errors = new ArrayList < BytecodeError > ();
  }

  /**
   * Adds an error to the report.
   *
   * @param an_error an error to be added
   */
  public void addError(final BytecodeError an_error) {
    my_errors.add(an_error);
  }

  /**
   * Returns true if there are no errors.
   *
   * @return true if there are no errors, false otherwise.
   */
  public boolean noErrors() {
    return my_errors.isEmpty();
  }

  /**
   * Retrieves an error at position a_pos in the report.
   *
   * @param a_pos a position of error
   * @return an error at position a_pos
   */
  public BytecodeError get(final int a_pos) {
    return my_errors.get(a_pos);
  }

  /**
   * Removes an error at position a_pos from the report.
   *
   * @param a_pos a position of error
   */
  public void remove(final int a_pos) {
    my_errors.remove(a_pos);
  }

  /**
   * Returns the length of the report.
   *
   * @return the length of the report
   */
  public int length() {
    return my_errors.size();
  }

  /**
   * Returns an array of errors reported by the report.
   *
   * @return an array of errors
   */
  public ArrayList < BytecodeError > getErrors() {
    return my_errors;
  }

}
