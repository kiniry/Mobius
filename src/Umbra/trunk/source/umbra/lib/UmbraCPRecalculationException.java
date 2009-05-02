/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import umbra.instructions.errors.ErrorReport;

/**
 * This is an exception raised when changing from "dirty" to "clean"
 * number of constant pool entries is impossible because the textual
 * representation of bytecode is malformed. <br> <br>
 *
 * @see BytecodeController#recalculateCPNumbers()
 *
 * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
 * @version a-01
 *
 */
public class UmbraCPRecalculationException extends UmbraException {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 1631183030211975455L;

  /**
   * Report containing description of errors that caused the exception.
   */
  private ErrorReport my_report;

  /**
   * Creates an exception caused by malformed bytecode.
   *
   * @param a_report report containing description of errors that caused
   * the exception
   */
  public UmbraCPRecalculationException(final ErrorReport a_report) {
    my_report = a_report;
  }

  /**
   * Returns report containing description of errors that caused the exception.
   *
   * @return report containing description of errors that caused the exception
   */
  public ErrorReport getReport() {
    return my_report;
  }

}
