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
   *  This field is <code>true</code> in case the wrong location is to be
   *  interpreted as a line. In case it is <code>false</code>, the wrong
   *  location is a position in the document.
   */
  private final boolean my_islinewrong;

  /**
   *  This field is <code>true</code> in case the document is a byte code
   *  document. Otherwise, the document is a Java source code document.
   */
  private final boolean my_doc_type;

  /**
   * Creates an exception with the information that the number of the line
   * outside the document. We assume that the document type here is byte code
   * document.
   *
   * @param a_loc the location outside the document
   * @param a_line <code>true</code> when the location is a line number,
   *   <code>false</code> when the location is a position number
   */
  public UmbraLocationException(final int a_loc, final boolean a_line) {
    my_wrong_location = a_loc;
    my_islinewrong = a_line;
    my_doc_type = true;
  }

  /**
   * Creates exception with the information that the number of the line outside
   * the document and a document type. We check two kinds of documents: byte
   * code documents and Java source code documents.
   *
   * @param a_doc_type the type of document for which the location exception is
   *   thrown: <code>true</code> for {@link umbra.editor.BytecodeDocument} and
   *   <code>false</code> for
   *   {@link org.eclipse.jdt.internal.ui.javaeditor.CompilationUnitEditor}
   * @param a_loc the location outside the document
   * @param a_line <code>true</code> when the location is a line number,
   *   <code>false</code> when the location is a position number
   */
  public UmbraLocationException(final boolean a_doc_type,
                                final int a_loc,
                                final boolean a_line) {
    my_wrong_location = a_loc;
    my_islinewrong = a_line;
    my_doc_type = a_doc_type;
  }

  /**
   * Returns the number of the wrong line.
   *
   * @return the number of the wrong line
   */
  public int getWrongLocation() {
    return my_wrong_location;
  }

  /**
   * Retruns <code>true</code> in case the editor is a byte code editor.
   * @return <code>true</code> in case the editor is a byte code editor,
   *   <code>false</code> otherwise
   */
  public boolean isByteCodeDocument() {
    return my_doc_type;
  }

  /**
   * Returns information on how to interpret the wrong location number.
   *
   * @return <code>true</code> when the wrong location number is to be
   *   interpreted as a line number, otherwise the location number is to be
   *   interpreted as a position in a document
   */
  public boolean isLineWrong() {
    return my_islinewrong;
  }
}
