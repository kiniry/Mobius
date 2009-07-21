/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

/**
 * This interface contains message priorities and bitmask
 * to control witch type of messages should be displayed.
 *
 * @see MLog
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class MessageLog {

  // message type bit masks:

  /**
   * Displays all messages.
   */
  public static final int MASK_PALL = 511;

  /**
   * For debug message that appear frequently,
   * trashing the console.
   */
  public static final int LEVEL_PDEBUG = 2;

  /**
   * Displays almost all messages.
   */
  public static final int MASK_PDEBUG = 510;

  /**
   * For debug message that appear very frequently
   * (or that are very long), slowing down the library.
   */
  public static final int LEVEL_PDEBUG2 = 1;

  /**
   * For displaying error messages.
   */
  public static final int LEVEL_PERROR = 256;

  /**
   * Displays only error and warning messages.
   */
  public static final int MASK_PERRORS = 384;

  // message types (priorities) - higher message type value,
  // higher it's priority:

  /**
   * For debug message that occur about once per
   * attribute operation (adding / modifying / removing
   *  / saving / loading / etc).
   */
  public static final int LEVEL_PINFO = 4;

  /**
   * Displays no messages.
   */
  public static final int MASK_PNONE = 0;

  /**
   * Normal verbosity level for developing
   * <code>bmllib</code>.
   */
  public static final int MASK_PNORMAL = 492;

  /**
   * For debug message that appears rarely, about once per
   * class operation (saving / loading / etc).
   */
  public static final int LEVEL_PNOTICE = 8;

  /**
   * For displaying messages while parsing with ANTLR.
   */
  public static final int LEVEL_PPARSER = 16;

  /**
   * Normal verbosity level for developing
   * <code>bmllib</code> + displays parser
   * failures and parsing progress.
   */
  public static final int MASK_PPARSER = 508;

  /**
   * For displaying progress while saving / loading.
   */
  public static final int LEVEL_PPROGRESS = 32;

  /**
   * Indicates that it's time to implement missing
   * code branch to make this test case run correctly.
   */
  public static final int LEVEL_PTODO = 64;

  /**
   * For displaying warning messages, eg. in situations in
   * which we are not certain what to do or that shouldn't
   * happen, but we're prepared for them.
   */
  public static final int LEVEL_PWARNING = 128;

  /**
   * An empty protected constructor to disallow the creation of instances
   * and allow private constructors in subclasses.
   */
  protected MessageLog() {
  }
}
