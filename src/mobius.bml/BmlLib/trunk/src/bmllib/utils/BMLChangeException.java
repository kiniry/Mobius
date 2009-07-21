/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package bmllib.utils;

/**
 * This class contains the code of the exception which informs the BMLLib
 * code consumers that the change in the code is improperly formed
 * (i.e. end before beginning, end after the end of the code, start less than
 * zero etc.)
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BMLChangeException extends Exception {

  /**
   * Serial ID used for serialisation.
   */
  private static final long serialVersionUID = 5725988177663553609L;

  /**
   * The constructor with string that explains the reason for the exception.
   *
   * @param string explanation of the exception
   */
  public BMLChangeException(final String string) {
    super(string);
  }
}
