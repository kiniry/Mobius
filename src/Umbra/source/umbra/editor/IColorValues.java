/*
 * Created on 2005-05-13
 *
 */
package umbra.editor;


/**
 * The interface defining colors used in particular coloring styles.
 *
 * @author Wojciech Wąs (ww209224@students.mimuw.edu.pl)
 * @version a-01
 */
public interface IColorValues {

  /**
   * The color of strings.
   */
  int STRING = 0;
  /**
   * The color of comments (starting with //).
   */
  int COMMENT = 1;
  /**
   * The color of unparsed text in bytecode (e.g. names of called methods).
   */
  int DEFAULT = 2;
  /**
   * The color of piece of bytecode recognized to be an error (not used).
   */
  int ERROR = 3;
  /**
   * The color of the method headers (e.g. public int a(int b)).
   */
  int HEADER = 4;

  /**
   * TODO.
   */
  int TAG = 5;
  /**
   * The color of bytecode instructions.
   */
  int BTC_INSTR = 7;
  /**
   * The color of the word: &ld;init&ge;.
   */
  int KEY = 8;
  /**
   * The color of bytecode keywords: "Attribute(s)", "LineNumber", etc.
   */
  int LINE = 9;
  /**
   * not used (but not to delete).
   */
  int THROWS = 10;
  /**
   * The color of numbers in bytecode that are surrounded by '( )'.
   */
  int SQUARE = 11;
  /**
   * The color of numbers appearing in bytecode except from cases listed
   * below.
   */
  int NUMBER = 12;
  /**
   * The color of line number at the beginning of a line.
   */
  int POSITION = 13;
  /**
   * The color of number arguments that are used with '#'.
   */
  int HASH = 14;
  /**
   * The color of number arguments that are used with '%'.
   */
  int ATTR = 15;
  /**
   * The color of BML annotations.
   */
  int ANNOT = 16;
  /**
   * The color of keywords in BML annotations.
   */
  int ANNOTKEY = 17;
  /**
   * Number of defined color constants.
   */
  int PARTS = 18;


  /**
   * TODO
   * The current colouring style is an index to the first coordinate
   * of the array.
   */
  int[][] MODELS = new int[][] {
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
