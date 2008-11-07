/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.textio;

import java.util.Vector;

import bmllib.utils.BMLChangeException;

import annot.bcclass.BCClass;
import annot.bcclass.MLog;

/**
 * This class represents BMl of an editing bytecode. It's
 * objects can be constructed  with {@link BCClass} and current
 * String representation of bytecode. You can add one or more
 * changes (using {@link #addChange(int, int, String)}
 * method), then execute these changes using
 * {@link #performChanges()} method (this will parse all
 * that changes merged to one, single change, updating
 * it's {@link BCClass}) and see that it's correct, than call
 * {@link #resetChanges()} method. If some changes has been
 * parsed outside this class, call {@link #resetChanges()}
 * to assume that {@link BCClass} is up to date.
 * It can parse only BML placed somewhere in bytecode,
 * not the bytecode itself. Bytecode changes won't be updated
 * into {@link BCClass}.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class CodeFragment extends CodeFragmentHelper {

  /**
   * Disable parsing single attributes; for debugging only.
   */
  private static final boolean GO_DISABLE_PARSER = false;

  /**
   * Flag which indicates if the code after preprocessing by
   * {@link #decorate(String)} should be shown in BMLLib log.
   */
  private static final boolean SHOW_DECORATED_CODE = true;

  /**
   * BCClass related with current bytecode.
   */
  private final BCClass bcc;

  /**
   * Position of the first character on which the old and the current
   * bytecodes differ.
   */
  private int begin;

  /**
   * Current bytecode.
   */
  private String code;

  /**
   * whether current bytecode is correct or not.
   */
  private boolean correct = true;

  /**
   * Position of first unaffected character (in current
   * bytecode).
   */
  private int end;

  /**
   * Last error message.
   */
  private String errMsg = "";

  /**
   * The flag is <code>true</code> in case some changes have been performed
   * using {@link #addChange(int, int, String)} since the last
   * {@link #resetChanges()} call.
   */
  private boolean modified;

  /**
   * Old (original) version of bytecode.
   */
  private String oldCode;

  /**
   * Common prefix for original and current bytecode.
   */
  private String prefix;

  /**
   * Common suffix for original and current bytecode.
   */
  private String suffix;

  /**
   * The vector with positions of BML regions. It is <code>null</code> before
   * the parsing is done for the current BML string.
   */
  private Vector < PosInCode > bml_positions;

  /**
   * A standard contructor.
   *
   * @param abcc - BCClass related with this bytecode,
   * @param acode - a String representation of bytecode.
   */
  public CodeFragment(final BCClass abcc, final String acode) {
    this.bcc = abcc;
    this.code = acode;
    this.oldCode = acode;
  }

  /**
   * Adds a change (effect of bytecode editing) to this
   * bytecode. A change is replacing one fragment of this
   * bytecode with another String.
   *
   * @param cfrom position of the first modified character
   * @param length length of the removed String
   * @param nc new String added at removed String's position
   * @throws BMLChangeException in case the range of change is improper
   */
  public void addChange(final int cfrom, final int length,
                        final String nc) throws BMLChangeException {
    final int cto = cfrom + length;
    addChangeErrorChecking(cfrom, cto);
    updateAddedArea(cfrom, nc, cto);
    this.bml_positions = null;
  }

  /**
   * Checks if the range of the removed area is properly formed.
   *
   * @param cfrom position of the first modified character
   * @param cto position of the first character after the removed area
   * @throws BMLChangeException in case the range of change is improper
   */
  private void addChangeErrorChecking(final int cfrom, final int cto)
    throws BMLChangeException {
    if (cfrom > cto) {
      throw new BMLChangeException("start of the region (" + cfrom +
                                   ") after the end (" + cto + ")");
    }
    if (cto > this.code.length()) {
      throw new BMLChangeException("end of the region (" + cto +
                                   ") after the code (" + this.code.length() +
                                   ")");
    }
    if (cfrom < 0) {
      throw new BMLChangeException("negative start of the region: " + cfrom);
    }
  }

  /**
   * @return current bytecode.
   */
  public String getCode() {
    return this.code;
  }

  /**
   * @return last error message.
   *     Currenlty error messages tells only if code were
   *     parsed by ANTLR, or was so incorrect that was
   *     rejected before passing it to ANTLR.
   */
  public String getErrMsg() {
    return this.errMsg;
  }

  /**
   * @return whether current bytecode is correct.
   *     It can ignore errors that are far enought from
   *     edited fragment (eg. if they were there at the
   *     beginnin, or before last {@link #resetChanges()}
   *     call.
   */
  public boolean isCorrect() {
    return this.correct;
  }

  /**
   * Modifies current bytecode, replacing given fragment
   * with another String and updating {@link BCClass}.
   * Either use this or sequently:<br>
   * - {@link #addChange(int, int, String)} (one or more
   *     times (for merged changes)),<br>
   * - {@link #performChanges()},<br>
   * - in case the parsed code is correct {@link #resetChanges()}.
   *
   * @param cfrom position of the first modified character
   * @param length length of the removed String
   * @param nc new String added at removed String's position
   * @throws BMLChangeException in case the range of change is improper
   * @see #addChange(int, int, String)
   */
  public void modify(final int cfrom,
                     final int length,
                     final String nc) throws BMLChangeException {
    addChange(cfrom, length, nc);
    performChanges();
    MLog.putMsg(MLog.LEVEL_PINFO, toString());
    if (this.correct) {
      resetChanges();
    }
  }

  /**
   * Propagates the current document change to the BMLLib AST.
   * First, checks that current bytecode is correct,
   * then parses it, affecting as few elements of BCClass
   * as it can.
   *
   * Currently, it parses just the whole bytecode file.
   */
  public void performChanges() {
    this.correct = true;
    this.errMsg = "";
    //DONE compute positions of affected code
    //FIXME implement that

    MLog.putMsg(MLog.LEVEL_PINFO, "code to be preprocessed:\n" + this.code);
    final String toparse = preProcess(this.code);
    if (SHOW_DECORATED_CODE) {
      MLog.putMsg(MLog.LEVEL_PINFO, "code to be parsed:\n" + addLines(toparse));
    }
    if (GO_DISABLE_PARSER) {
      return;
    }
    //DONE create grammar for parsing bytecode

    this.correct = this.bcc.getParser().parseClass(toparse, false);
    //DONE and parse it into bcc.
    if (this.correct) {
      this.bcc.getParser().parseClass(toparse, true);
    }
    bml_positions = this.bcc.getParser().getBMLPositions();
    this.errMsg = this.bcc.getParser().getErrMsg();
  }

  /**
   * Adds line numbers in front of each line. This is a helper method for
   * debugging purposes.
   *
   * @param scode string to add the line numbers to
   * @return the string with added line numbers
   */
  private String addLines(final String scode) {
    final StringBuffer buf = new StringBuffer();
    final String[] lns = scode.split("\n");
    for (int i = 0; i < lns.length; i++) {
      buf.append("" + i + " -> " + lns[i] + "\n");
    }
    return buf.toString();
  }

  /**
   * Assumes that bytecode has been parsed succesfuly.
   * It should be called after each
   * {@link #performChanges()} call, if bytecode is correct.
   * Calling it for incorrect bytecode may result of ignoring
   * some errors in next parsing attempt.
   * This method has been separated from
   * {@link #performChanges()} method only for test
   * pusposes, to show {@link CodeFragment}'s state
   * just after parsing it.
   */
  public void resetChanges() {
    this.oldCode = this.code;
    this.begin = -1;
    this.end = -1;
    this.prefix = null;
    this.suffix = null;
    this.modified = false;
  }

  /**
   * Displays current state of this bytecode fragment.
   *
   * @return the text representation of the current fragment
   */
  public String toString() {
    if (!this.modified) {
      return "code hasn't been modified yet";
    }
    String ret = "";
    /*
    String ret = "******** removed code: *********\n";
    ret += this.toRemove;
    ret += "\n*** current (modified) code: ***\n";
    ret += this.prefix + "##" + this.toAdd + "##" + this.suffix;
    ret += "\n*** CodeFragment status: ***";
    ret += "\ntotal length: " + this.code.length();
    ret += "\nchanged fragment: " + this.begin + " to " + this.end;
    ret += "\ncode is currently " + (this.correct ? "correct" : "incorrect");
    */
    if (this.errMsg.length() > 0) {
      ret += "\nlast error message: " + this.errMsg;
    }
    return ret;
  }

  /**
   * This method updates the area of the code which is modified. The arguments
   * of the method describe the new affected area which should be added to
   * the representation of the current fragment.
   *
   * @param cfrom position of the first modified character
   * @param nc the string which is to be added to the area
   * @param cto position of the first character after the removed area
   */
  private void updateAddedArea(final int cfrom, final String nc,
                               final int cto) {
    if (!this.modified) {
      this.begin = cfrom;
      this.end = cto;
      this.modified = true;
      this.oldCode = code;
    } else {
      if (cfrom < this.begin) {
        this.begin = cfrom;
      }
      if (cto > this.end) {
        this.end = cto;
      }
    }
    this.code = this.code.substring(0, cfrom) + nc + this.code.substring(cto);
  }

  /**
   * Returns the last correct version of the code.
   *
   * @return the string with the last correct version of the code
   */
  public String getLastCorrectCode() {
    return oldCode;
  }
}
