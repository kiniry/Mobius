/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.instructions;

/**
 * This class is used to mark possible errors in quick dispatcher automaton
 * {@link DispatchingAutomaton}.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class CannotCallRuleException extends Exception {

  /**
   * The serial ID for this class.
   */
  private static final long serialVersionUID = 6117443445094038369L;

  /**
   * This method creates the exception with the given reason that
   * was handed in by some calculations before.
   *
   * @param an_ex the exception which is the reason
   */
  public CannotCallRuleException(final Throwable an_ex) {
    super(an_ex);
  }
}
