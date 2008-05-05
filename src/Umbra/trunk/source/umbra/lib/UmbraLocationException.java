/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import org.eclipse.jface.text.IDocument;

import umbra.editor.BytecodeDocument;

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
   *  This field is <code>true</code> in case the document is a byte code
   *  document. Otherwise, the document is a Java source code document.
   */
  private final boolean my_doc_type;

  /**
   * Creates an exception with the information that the number of the line
   * outside the document. We assume that the document type here is byte code
   * document.
   *
   * @param a_line the line location outside the document
   */
  public UmbraLocationException(final int a_line) {
    my_wrong_location = a_line;
    my_doc_type = true;
  }

  /**
   * Creates exception with the information that the number of the line outside
   * the document and a document type. We check two kinds of documents: byte
   * code documents and Java source code documents.
   *
   * @param a_doc the document for which the location exception is thrown
   * @param a_line the line location outside the document
   */
  public UmbraLocationException(final IDocument a_doc, final int a_line) {
    my_wrong_location = a_line;
    if (a_doc instanceof BytecodeDocument) {
      my_doc_type = true;
    } else {
      my_doc_type = false;
    }
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
}
