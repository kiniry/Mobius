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
 * This is an exception used to trace situations when a syntax error is
 * encountered in the parsing of a BML document.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class UmbraSyntaxException extends Exception {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 6561716806388549111L;


  /**
   *  This field contains the line number which contains the syntax error.
   */
  private final int my_wrong_line;

  /**
   * Creates an exception with the information on which line caused the error.
   *
   * @param the_line the line with the syntax error
   */
  public UmbraSyntaxException(final int the_line) {
    my_wrong_line = the_line;
  }

  /**
   * Returns the number of the wrong line.
   *
   * @return the number of the wrong line
   */
  public int getWrongLine() {
    return my_wrong_line;
  }
}
