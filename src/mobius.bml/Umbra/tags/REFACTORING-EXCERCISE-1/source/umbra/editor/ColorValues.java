/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) ${date} University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package umbra.editor;


/**
 * The interface defining colors used in particular coloring styles.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public class ColorValues {

  /**
   * TODO.
   */
  public static final int RED_COMPONENT = 0;

  /**
   * TODO.
   */
  public static final int GREEN_COMPONENT = 1;

  /**
   * TODO.
   */
  public static final int BLUE_COMPONENT = 2;

  /**
   * TODO.
   */
  public static final int STYLE_COMPONENT = 0;

  /**
   * The number of style parameters per slot. Currently, we have paramters
   * for color components red, green, blue and text style.
   */
  public static final int CN = 4;

  /**
   * The color of strings.
   */
  public static final int STRING = 0;
  /**
   * The color of comments (starting with //).
   */
  public static final int COMMENT = 1;
  /**
   * The color of unparsed text in bytecode (e.g. names of called methods).
   */
  public static final int DEFAULT = 2;
  /**
   * The color of piece of bytecode recognized to be an error (not used).
   */
  public static final int ERROR = 3;
  /**
   * The color of the method headers (e.g. public int a(int b)).
   */
  public static final int HEADER = 4;

  /**
   * TODO.
   */
  public static final int TAG = 5;
  /**
   * The color of bytecode instructions.
   */
  public static final int BTC_INSTR = 7;
  /**
   * The color of the word: &ld;init&ge;.
   */
  public static final int KEY = 8;
  /**
   * The color of bytecode keywords: "Attribute(s)", "LineNumber", etc.
   */
  public static final int LINE = 9;
  /**
   * not used (but not to delete).
   */
  public static final int THROWS = 10;
  /**
   * The color of numbers in bytecode that are surrounded by '( )'.
   */
  public static final int SQUARE = 11;
  /**
   * The color of numbers appearing in bytecode except from cases listed
   * below.
   */
  public static final int NUMBER = 12;
  /**
   * The color of line number at the beginning of a line.
   */
  public static final int POSITION = 13;
  /**
   * The color of number arguments that are used with '#'.
   */
  public static final int HASH = 14;
  /**
   * The color of number arguments that are used with '%'.
   */
  public static final int ATTR = 15;
  /**
   * The color of BML annotations.
   */
  public static final int ANNOT = 16;
  /**
   * The color of keywords in BML annotations.
   */
  public static final int ANNOTKEY = 17;
  /**
   * Number of defined color constants.
   */
  public static final int PARTS = 18;


  /**
   * TODO
   * The current colouring style is an index to the first coordinate
   * of the array.
   */
  public static final int[][] MODELS = new int[][] {
    new int[] {0, 0, 255, 0,
               0, 0, 0, 2, 0, 0, 0, 0, 255, 0, 0, 0,
               0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1,
               0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
               0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
               0, 0, 0, 2, 0, 0, 0, 2,
               0, 0, 0, 2, 0, 0, 0, 3},
    new int[] {0, 255, 0, 0,
               128, 128, 128, 2,
               0, 0, 0, 0,
               255, 0, 0, 0,
               0, 0, 0, 1,
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
               10, 94, 13, 1, //default BML annotation colour
               153, 255, 153, 1},
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
               153, 255, 153, 1},
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
               128, 192, 64, 0,
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
               128, 128, 128, 0,
               128, 128, 128, 0}
  };
}
