/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions.errors;

import org.apache.bcel.classfile.Method;

/**
 * This class represents an error of referencing non-existing constant
 * from java class method.
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class MethodNoSuchConstantError extends NoSuchConstantError {

  /**
   * Method that has references to non-existing constants.
   */
  private Method my_cause;

  /**
   *
   * @param a_method a method that has references to non-existing constants
   */
  public void setMethod(final Method a_method) {
    my_cause = a_method;
  }

  /**
   * @return description of the cause of the error
   */
  public String[] getCauses() {
    return new String[] {"Method, name index: " + my_cause.getNameIndex() +
                         ", signature index: " + my_cause.getSignatureIndex()};
  }

  /**
   * Returns textual representation of the error.
   *
   * @return a string with error message
   */
  public String getShortErrorMessage() {
    return super.getErrorMessage() + " (method)";
  }

}
