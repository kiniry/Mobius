/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import umbra.instructions.errors.BytecodeError;

/**
 * This is an exception raised when changing from "dirty" to "clean"
 * number of constant pool entries in case the "dirty" number refers
 * to non existing constant. <br> <br>
 *
 * @see BytecodeController#recalculateCPNumbers()
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class UmbraNoSuchConstantException extends UmbraException {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 1632181230181959472L;

  /**
   * Detailed information about exception cause.
   */
  private BytecodeError my_error;

  /**
   * Creates an exception caused by reference to non existent constant.
   *
   * @param an_error detailed information about exception cause
   */
  public UmbraNoSuchConstantException(final BytecodeError an_error) {
    my_error = an_error;
  }

  /**
   * Returns detailed information about exception cause.
   *
   * @return detailed information about exception cause
   */
  public BytecodeError getError() {
    return my_error;
  }

}
