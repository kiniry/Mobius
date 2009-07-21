/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.lib;

import org.eclipse.jface.text.DocumentEvent;

import bmllib.utils.BMLChangeException;

import annot.bcclass.BCClass;
import annot.textio.CodeFragment;

/**
 * This class is responsible for communication with BMLLib
 * library (except code position synchronization, that calls
 * only stateless, static methods from BMLLib). It stores only
 * official copies of BCClass, which represents BML-annotated
 * bytecode. All the JavaClass' that are used in Umbra editor
 * should be the same (==) as the one in the corresponding BCClass
 * (accessible via {@link #getBcc()}.getJc()).
 *
 * There is one BMLParsing object per one open editor.
 *
 * FIXME: make sure all the communication with BMLlib goes through this class
 *   https://mobius.ucd.ie/ticket/592
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BMLParsing {

  /**
   * This represents BML-annotated byte code whose code
   * (if correct) is displayed in the editor.
   */
  private BCClass my_bcc;

  /**
   * This represents BML-annotated byte code (the same as in
   * <code>my_bcc</code> with its current (maybe incorrect)
   * string representation and its changes since last time
   * it was correct.
   */
  private CodeFragment my_cFgmt;

  /**
   * A standard constructor. Should be used just after loading
   * a JavaClass (from file and then into BCClass).
   *
   * @param a_bcc BCClass representing bytecode in editor this
   *    object is related with. Editor's initial code should
   *    be the same as (.equal()) <code>bcc.printCode()</code>
   *    returns.
   */
  public BMLParsing(final BCClass a_bcc) {
    this.my_bcc = a_bcc;
    final String code = a_bcc.printCode();
    this.my_cFgmt = new CodeFragment(a_bcc, code);
  }

  /**
   * This method should be called on every bytecode document's
   * change. It parses changes made in the document into
   * its BCClass (if document is correct) and displays proper
   * message (that bytecode is correct or incorrect) in the
   * status bar.
   *
   * @param an_event -DocumentEvent describing document changes
   *    currently made, eg. event parameter of
   *    <code>documentChanged()</code> in editor's listener.
   * @throws BMLChangeException in case the range of change is improper
   */
  public void onChange(final DocumentEvent an_event) throws BMLChangeException {
    String msg = "";
    my_cFgmt.modify(an_event.fOffset, an_event.fLength, an_event.fText);
    msg += "annotations status: ";
    if (my_cFgmt.isCorrect()) {
      msg += "correct";
    } else {
      msg += "incorrect";
    }
    if (!my_cFgmt.isCorrect())
      if (my_cFgmt.getErrMsg() != null)
        msg += ": " + my_cFgmt.getErrMsg();
  }

  /**
   * @return current bytecode (ast) with BML annotations.
   *    It is an official copy that all other classes related
   *    with the same editor should reference to (to make
   *    any changes in the bytecode).
   */
  public BCClass getBcc() {
    return my_bcc;
  }

  /**
   * This method changes the textual representation of the byte code
   * source.
   *
   * @param a_code the new code to associate
   */
  public void setCodeString(final String a_code) {
    my_cFgmt = new CodeFragment(my_bcc, a_code);
  }

  /**
   * This method checks if the last parsed fragment is correct.
   *
   * @return <code>true</code> in case the fragment is correct,
   *   <code>false</code> otherwise
   */
  public boolean isCorrect() {
    return my_cFgmt.isCorrect();
  }

  /**
   * This method return the error message for the last parsed fragment.
   *
   * @return the error message for the last parsed fragment
   */
  public String getErrorMsg() {
    return my_cFgmt.getErrMsg();
  }
}
