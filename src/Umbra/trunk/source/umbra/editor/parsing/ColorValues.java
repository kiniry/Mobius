/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor.parsing;


/**
 * The interface defining colours used in particular colouring styles.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public final class ColorValues {

  /**
   * The position of the red colour component in a single style entry from
   * {@link #MODES_DESC} array.
   */
  public static final int COMPONENT_RED = 0;

  /**
   * The position of the green colour component in a single style entry from
   * {@link #MODES_DESC} array.
   */
  public static final int COMPONENT_GREEN = 1;

  /**
   * The position of the blue colour component in a single style entry from
   * {@link #MODES_DESC} array.
   */
  public static final int COMPONENT_BLUE = 2;

  /**
   * The position of the font style component in a single style entry from
   * {@link #MODES_DESC} array.
   */
  public static final int COMPONENT_TXTSTYLE = 3;

  /**
   * The number of style parameters per slot. Currently, we have paramters
   * for colour components red, green, blue and text style.
   */
  public static final int COMPONENT_NUMBER = COMPONENT_TXTSTYLE + 1;

  /**
   * The colour of strings.
   */
  public static final int SLOT_STRING = 0;

  /**
   * The colour of comments.
   */
  public static final int SLOT_COMMENT = 1;

  /**
   * The colour of unparsed text in byte code (e.g. names of called methods).
   */
  public static final int SLOT_DEFAULT = 2;

  /**
   * The colour of pieces of byte code recognized to be an error (not used).
   */
  public static final int SLOT_ERROR = 3;

  /**
   * The colour of the method headers (e.g. public int a(int b)).
   */
  public static final int SLOT_HEADER = 4;

  /**
   * The colour of BML annotations.
   */
  public static final int SLOT_TAG = 5;

  /**
   * The color of bytecode instructions.
   */
  public static final int SLOT_BTCINSTR = 7;

  /**
   * The colour of the word: &ld;init&ge;. Currently unused.
   */
  public static final int SLOT_KEY = 8;

  /**
   * The colour of the "LineNumber" areas.
   * FIXME: add handling of "Line" areas https://mobius.ucd.ie/ticket/547
   */
  public static final int SLOT_LINE = 9;

  /**
   * The colour of the "Throws" areas.
   * FIXME: add handling of "Line" areas https://mobius.ucd.ie/ticket/549
   */
  public static final int SLOT_THROWS = 10;

  /**
   * The colour of sections in byte code that are surrounded by '( )' or '{ }'.
   */
  public static final int SLOT_PARENTHESES = 11;

  /**
   * The color of numbers appearing in byte code except from cases listed
   * below.
   */
  public static final int SLOT_NUMBER = 12;

  /**
   * The colour of line number at the beginning of a line.
   */
  public static final int SLOT_LABELNUMBER = 13;

  /**
   * The colour of number arguments that start with '#'.
   */
  public static final int SLOT_HASH = 14;

  /**
   * The colour of number arguments that start with '%'.
   */
  public static final int SLOT_PERCENT = 15;

  /**
   * The colour of the BML annotations.
   */
  public static final int SLOT_BML = 16;

  /**
   * The colour of keywords in the BML annotations.
   */
  public static final int SLOT_BMLKEYWORDS = 16;

  /**
   * Number of defined colour constants.
   */
  public static final int SLOTS_NO = 18;


  /**
   * The array which associates colour and text style modes with actual
   * values of the RGB colours. The colouring mode is an index to the first
   * coordinate of the array, the particular colour parameters are start
   * at the position: slot_number * {@link #COMPONENT_NUMBER}. The style
   * components are located at the following positions:
   * <ul>
   *   <li>slot_number * {@link #COMPONENT_NUMBER} +
   *       {@link #COMPONENT_RED},</li>
   *   <li>slot_number * {@link #COMPONENT_NUMBER} +
   *       {@link #COMPONENT_GREEN},</li>
   *   <li>slot_number * {@link #COMPONENT_NUMBER} +
   *       {@link #COMPONENT_BLUE},</li>
   *   <li>slot_number * {@link #COMPONENT_NUMBER} +
   *       {@link #COMPONENT_TXTSTYLE},</li>
   * </ul>
   *
   * The available slots are:
   * {@link #SLOT_STRING},
   * {@link #SLOT_COMMENT}, {@link #SLOT_DEFAULT}, {@link #SLOT_ERROR},
   * {@link #SLOT_HEADER}, {@link #SLOT_TAG}, {@link #SLOT_BTCINSTR},
   * {@link #SLOT_KEY}, {@link #SLOT_LINE}, {@link #SLOT_THROWS},
   * {@link #SLOT_PARENTHESES}, {@link #SLOT_NUMBER}, {@link #SLOT_LABELNUMBER},
   * {@link #SLOT_HASH}, {@link #SLOT_PERCENT}, {@link #SLOT_BML},
   * {@link #SLOT_BMLKEYWORDS}.
   *
   */
  public static final int[][] MODES_DESC = new int[][] {
    new int[] {0, 0, 255, 0,
               0, 0, 0, 2, 0, 0, 0, 0, 255, 0, 0, 0,
               0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1,
               0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
               0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
               0, 0, 0, 2, 0, 0, 0, 2,
               0, 0, 0, 2, 0, 0, 0, 3},
    new int[] {0, 255, 0, 0,
               128, 128, 128, 2,
               200, 0, 0, 0,
               255, 0, 0, 0,
               200, 0, 0, 1,
               0, 0, 128, 0,
               0, 0, 128, 0,
               2, 27, 251, 0, //default bytecode instruction colour
               0, 0, 255, 1,
               0, 192, 128, 0,
               0, 192, 128, 0,
               0, 128, 64, 0,
               94, 71, 58, 1,
               94, 71, 58, 1,
               13, 68, 189, 0,
               13, 68, 189, 0,
               10, 94, 13, 0, //default BML annotation colour
               10, 94, 13, 3}, //default BML kyeword annotation colour
    new int[] {0, 255, 0, 0,
               128, 128, 128, 2,
               0, 0, 0, 0,
               255, 0, 0, 0,
               0, 0, 0, 1,
               0, 0, 128, 0,
               0, 0, 128, 0,
               255, 160, 0, 3,
               0, 0, 255, 1,
               0, 192, 128, 0,
               0, 192, 128, 0,
               0, 128, 64, 0,
               255, 224, 0, 1,
               255, 224, 0, 1,
               224, 255, 0, 3,
               224, 0, 255, 3,
               255, 153, 204, 0,
               255, 153, 204, 3},
    new int[] {0, 0, 255, 0,
               255, 128, 255, 2,
               64, 0, 64, 0,
               255, 64, 0, 1,
               192, 0, 192, 1,
               128, 0, 128, 0,
               128, 0, 128, 0,
               128, 0, 255, 1,
               128, 0, 128, 0,
               128, 0, 192, 0,
               192, 0, 192, 0,
               192, 0, 192, 0,
               128, 0, 128, 1,
               128, 0, 128, 1,
               255, 0, 255, 1,
               255, 0, 255, 1,
               255, 128, 255, 2,
               255, 0, 255, 3},
    new int[] {128, 128, 0, 0,
               192, 192, 192, 0,
               128, 128, 128, 0,
               255, 0, 0, 1,
               64, 64, 64, 1,
               128, 128, 128, 0,
               128, 128, 128, 0,
               64, 64, 64, 1,
               128, 128, 128, 1,
               128, 128, 128, 1,
               64, 64, 64, 1,
               255, 192, 128, 1,
               0, 192, 0, 1,
               0, 192, 0, 1,
               192, 192, 0, 1,
               192, 192, 0, 1,
               192, 192, 192, 2,
               192, 192, 192, 3},
    new int[] {0, 255, 255, 0,
               128, 128, 128, 0,
               0, 0, 0, 0,
               255, 0, 0, 2,
               0, 0, 0, 0,
               0, 128, 128, 0,
               0, 128, 128, 0,
               0, 128, 128, 0,
               0, 128, 128, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0},
    new int[] {0, 0, 255, 0,
               0, 128, 0, 0,
               0, 0, 0, 0,
               255, 0, 0, 0,
               128, 0, 64, 1,
               0, 64, 128, 0,
               0, 64, 128, 0,
               64, 0, 64, 1,
               64, 0, 64, 1,
               128, 0, 128, 0,
               128, 0, 64, 1,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 0, 0, 0,
               0, 128, 0, 0,
               0, 128, 0, 1},
    new int[] {64, 255, 96, 0,
               160, 0, 128, 1,
               192, 64, 255, 2,
               96, 160, 0, 3,
               128, 192, 65, 0,
               255, 96, 160, 1,
               0, 128, 192, 2,
               192, 128, 0, 3,
               160, 96, 255, 0,
               64, 192, 128, 1,
               0, 160, 96, 2,
               255, 64, 192, 3,
               128, 0, 160, 0,
               96, 255, 64, 1,
               64, 255, 96, 2,
               160, 0, 128, 3,
               192, 64, 255, 0,
               96, 160, 0, 1},
    new int[] {128, 128, 128, 0,
               128, 128, 127, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0,
               128, 128, 128, 0}
  };

  /**
   * The private constructor to forbid the creation of objects with this type.
   */
  private ColorValues() {
  }
}
