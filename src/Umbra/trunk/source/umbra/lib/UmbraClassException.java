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
 * This is an exception used to trace situations when a problem with class
 * file is encountered. It is used to encapsulate {@link ClassNotFoundException}
 * or {@link annot.io.ReadAttributeException}
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class UmbraClassException extends Exception {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 1344810623005640402L;

  /**
   *  This field contains the exception which triggered the current one.
   */
  private final Exception my_exception;

  /**
   * Creates an exception with the exception that caused the current one.
   *
   * @param an_exception the exception which caused the current one
   */
  public UmbraClassException(final Exception an_exception) {
    my_exception = an_exception;
  }

  /**
   * Returns the exception which caused the current one.
   *
   * @return the exception which caused the current one
   */
  public Exception getCause() {
    return my_exception;
  }

}
