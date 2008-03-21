/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;

/**
 * This is an exception used to trace situations when the parsing exceeded
 * the content of a document.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class UmbraLocationException extends Exception {

  /**
   * The serial number of the class.
   */
  private static final long serialVersionUID = 1368987676616348613L;

  /**
   *  This field contains the location which is considered to be wrong.
   */
  private final int my_wrong_location;

  /**
   * Creates exception with the information that the number of the line outside
   * the document.
   *
   * @param a_line the line location outside the document
   */
  public UmbraLocationException(final int a_line) {
    my_wrong_location = a_line;
  }

  /**
   * Returns the number of the wrong line.
   *
   * @return the number of the wrong line
   */
  public int getWrongLocation() {
    return my_wrong_location;
  }

}
