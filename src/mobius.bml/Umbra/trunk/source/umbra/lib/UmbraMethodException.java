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
 * This is an exception used to trace situations when the processing reached
 * a method which does not exist in the document being processed.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 *
 */
public class UmbraMethodException extends Exception {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 5973766671008411853L;

  /**
   *  This field contains the method number which is considered to be wrong.
   */
  private final int my_wrong_methodno;

  /**
   * Creates an exception with the information on the number of the method
   * outside the document.
   *
   * @param a_mno the method number outside the document
   */
  public UmbraMethodException(final int a_mno) {
    my_wrong_methodno = a_mno;
  }

  /**
   * Returns the number of the wrong method.
   *
   * @return the number of the wrong method
   */
  public int getWrongMethodNumber() {
    return my_wrong_methodno;
  }
}
