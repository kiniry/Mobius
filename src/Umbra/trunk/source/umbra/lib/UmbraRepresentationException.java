/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;


/**
 * This is an exception used to trace situations when the internal
 * representation of the bytecode could not be established. It is used to
 * encapsulate different kinds of exceptions thrown from within the
 * {@link umbra.instructions.BytecodeController}.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class UmbraRepresentationException extends Exception {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 1368987676616344613L;

  /**
   * The cause of the current exception.
   */
  private final Exception my_cause;

  /**
   * The constructor which constructs the exception with the given cause.
   *
   * @param a_cause the cause of the exception
   */
  public UmbraRepresentationException(final Exception a_cause) {
    my_cause = a_cause;
  }

  /**
   * Returns a textual description of the problem that caused the exception.
   *
   * @return the description of the problem
   */
  public String getProblemDescription() {
    String report = my_cause.toString();
    if (my_cause instanceof UmbraLocationException) {
      final UmbraLocationException new_name = (UmbraLocationException) my_cause;
      report = "Wrong position " + new_name.getWrongLocation() + " ";
      if (new_name.isByteCodeDocument()) {
        report += "in the bytecode document";
      } else {
        report += "in the Java source code document";
      }
    } else if (my_cause instanceof UmbraMethodException) {
      final UmbraMethodException new_name = (UmbraMethodException) my_cause;
      report = "Wrong method number " + new_name.getWrongMethodNumber();
    }
    if (my_cause instanceof UmbraSyntaxException) {
      final UmbraSyntaxException new_name = (UmbraSyntaxException) my_cause;
      report = "Syntax error in the line number " + new_name.getWrongLine();
    }
    return report;
  }
}
