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
 * This class represents an error of constant pool entry or instruction
 * referencing non existing constant.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class NoSuchConstantError extends BytecodeError {

  /**
   * The constant numbers of the non existing constants.
   */
  private ArrayList < Integer > my_numbers = new ArrayList < Integer > ();

  /**
   * Returns the constant numbers of the non existing constants.
   *
   * @return the constant number
   */
  public Integer[] getNumber() {
    return (Integer[]) my_numbers.toArray();
  }

  /**
   * Sets a line in which an error occured.
   *
   * @param a_line a line to be set
   */
  public void addLine(final BytecodeLineController a_line) {
    setLine(a_line);
  }

  /**
   * Adds a number of non existing constant to the list.
   *
   * @param a_number a number of non existing constant
   */
  public void addNumber(final int a_number) {
    my_numbers.add(a_number);
  }

  /**
   *
   * @return string containing the numbers of constants which caused the error
   */
  private String getNumbers() {
    String res = "";
    if (my_numbers.size() == 1) return res + " #" + my_numbers.get(0);
    for (int i = 0; i <  my_numbers.size() - 1; i++) {
      res += " #" + my_numbers.get(i) + ",";
    }
    return res + " #" + my_numbers.get(my_numbers.size() - 1);
  }

  /**
   * Returns textual representation of the error.
   *
   * @return a string with error message
   */
  public String getShortErrorMessage() {
    final String res = "Reference in bytecode to non existing constants";
    return res + getNumbers();
  }

  /**
   * Returns textual representation of the error intended to
   * be used with line contents. I.e.: <br> <br>
   *
   * Reference in constant pool to non existing constants #5: <br>
   * const #1 = String #5; <br>
   *
   * @return a string with error message
   */
  public String getErrorMessage() {
    final String res = "Reference in bytecode to non existing constants";
    return res + getNumbers() + ":";
  }

}
