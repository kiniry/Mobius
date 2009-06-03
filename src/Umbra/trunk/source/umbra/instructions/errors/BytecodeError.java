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
import umbra.instructions.ast.BytecodeLineController;

/**
 * This class represents an error in textual bytecode representation.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public abstract class BytecodeError {

  /**
   * List of editor lines in which an error occured.
   */
  private ArrayList < BytecodeLineController > my_lines;

  /**
   * Default constructor.
   */
  public BytecodeError() {
    my_lines = new ArrayList < BytecodeLineController > ();
  }

  /**
   * Retrieves description of places in which an error occured.
   * Default usage is editor lines in which error occured, but some
   * subclasses may override it.
   *
   * @return description of places in which an error occured
   */
  public String[] getCauses() {
    final String[] desc = new String[my_lines.size()];
    int i = 0;
    for (BytecodeLineController blc : my_lines) {
      desc[i] = blc.getLineContent();
      i++;
    }
    return desc;
  }

  /**
   * Adds a line to the list of lines in which an error occured.
   *
   * @param a_line a line to be added
   */
  public void addLine(final BytecodeLineController a_line) {
    my_lines.add(a_line);
  }

  /**
   * Sets a line in which an error occured. Used by subclasses that
   * represent single-line error.
   *
   * @param a_line a line to be set
   */
  protected void setLine(final BytecodeLineController a_line) {
    my_lines.clear();
    my_lines.add(a_line);
  }

  /**
   * Returns textual representation of the error.
   *
   * @return a string with error message
   */
  public String getShortErrorMessage() {
    return "Error";
  }

  /**
   * Returns textual representation of the error intended to
   * be used with line contents. I.e.: <br> <br>
   *
   * Error in following lines: <br>
   * 0: ldc <br>
   * 1: iadd <br>
   *
   * @return a string with error message
   */
  public String getErrorMessage() {
    return "Error in following lines:";
  }

}
