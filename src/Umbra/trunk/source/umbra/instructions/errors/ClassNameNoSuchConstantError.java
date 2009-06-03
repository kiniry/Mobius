/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.errors;

/**
 * This class represents an error of referencing non-existing constant
 * from java class as class name index.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class ClassNameNoSuchConstantError extends NoSuchConstantError {

  /**
   *
   * @param a_constant a number of non-existing constant that
   * caused the error
   */
  public ClassNameNoSuchConstantError(final int a_constant) {
    super();
    addNumber(a_constant);
  }

  /**
   * @return description of the cause of the error
   */
  public String[] getCauses() {
    return new String[] {"Class name index"};
  }

  /**
   * Returns textual representation of the error.
   *
   * @return a string with error message
   */
  public String getShortErrorMessage() {
    return super.getErrorMessage() + " (class name index)";
  }

}
