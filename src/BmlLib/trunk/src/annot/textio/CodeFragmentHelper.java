/**
 *
 */
package annot.textio;

/**
 * This class represents contains the helper methods for the
 * {@link CodeFragment} class. The methods here handle the preprocessing of
 * the program text which removes all the start-of-the-line marks for BML
 * areas.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class CodeFragmentHelper {


  /**
   * A protected constructor to prevent constructing instances by non
   * sublcasses.
   */
  protected CodeFragmentHelper() {
  }

  /**
   * Translates line number of a String to character number
   * (offset).
   *
   * @param code - multi-line String,
   * @param lnr - number of line in <code>code</code>.
   * @return Offset of first character of <code>lnr</code>'s
   *     line in <code>code</code>.
   */
  public static int getLineOffset(final String code, final int lnr) {
    final String[] lines = code.split("\n");
    int pos = 0;
    for (int i = 0; i < lnr; i++) {
      pos += lines[i].length() + 1;
    }
    return pos;
  }

  /**
   * This method strips out the one-line comments and BML signs @ at the
   * beginning of a line, but inside a BML comment.
   *
   * @param code the bytecode with BML to preprocess
   * @return the preprocessed code
   */
  public static String preProcess(final String code) {
    final StringBuffer buf = new StringBuffer(code.length());
    int i = 0;
    while (i < code.length()) {
      char ch = code.charAt(i);
      if (ch == '"') {
        final int opos = i;
        i = readString(i, code);
        buf.append(code.substring(opos, i));
        continue;
      } else if (ch == '/') { // DisplayStyle.BML_COMMENT_START starts with '/'
        i++;
        ch = code.charAt(i);
        if (ch == '/' &&
            !code.substring(i + 1).startsWith(DisplayStyle.BML_AT_SIGN)) {
          i = readTillEOL(i, code);
          continue;
        } else if (code.substring(i).startsWith(
                                                DisplayStyle.BML_COMMENT_START
                                                    .substring(1))) {
          buf.append('/');
          i = readBMLComment(i, code, buf);
          continue;
        } else {
          buf.append('/');
        }
      }
      buf.append(ch);
      i++;
    }
    return buf.toString();
  }


  /**
   * This method reads in the text till the end of the current line. It
   * returns the position of the newline character (\n) or
   * the value equal to the length of the string.
   *
   * @param pos the position to start the reading of the line
   * @param code the text to read the line from
   * @return the position of the end-of-line marker
   */
  private static int readTillEOL(final int pos, final String code) {
    int i = pos + 1;
    while (i < code.length()) {
      final char ch = code.charAt(i);
      if (ch == '\n') {
        return i;
      }
      i++;
    }
    return i;
  }

  /**
   * This method reads in the text till the end of the string mark ("). It
   * recognises all the Java string escape sequences (such as \\ etc.). It
   * returns the position of the first character after the final " or
   * the value equal to the length of the string.
   *
   * @param pos the position to start the reading of the line
   * @param code the text to read the line from
   * @return the position of the end-of-line marker
   */
  private static int readString(final int pos, final String code) {
    int i = pos + 1;
    while (i < code.length()) {
      char ch = code.charAt(i);
      if (ch == '\\') {
        i++;
        ch = code.charAt(i);
        continue;
      } else if (ch == '"') {
        return ++i;
      }
      i++;
    }
    return i;
  }

  /**
   * The method reads in a BML comment removing the @ signs at the beginnings
   * of internal lines. It reads string from the <code>code</code> parameter.
   * The first character to be read is pointed by the <code>pos</code>
   * parameter. The resulting string is appended to the <code>buf</code>
   * parameter. The result is the position of the first character in
   * <code>code</code>which has not been swallowed in the course of the
   * processing. This method assumes that <code>pos</code> is inside of a
   * BML comment.
   *
   * @param pos the position of the first character to read
   * @param code the string to read characters from
   * @param buf the string to append characters to
   * @return the position of the first character that was not read by the
   *   procedure
   */
  private static int readBMLComment(final int pos, final String code,
                                    final StringBuffer buf) {
    int i = pos;
    boolean newline = false;
    while (i < code.length()) {
      final char ch = code.charAt(i);
      if (DisplayStyle.BML_AT_SIGN.charAt(0) == ch && newline) {
        newline = false;
        if (code.substring(i).startsWith(DisplayStyle.BML_COMMENT_END)) {
          buf.append(DisplayStyle.BML_COMMENT_END);
          return i + DisplayStyle.BML_COMMENT_END.length();
        } else {
          i++;
          continue;
        }
      } else if (ch == '\n') {
        newline = true;
      } else if (!Character.isWhitespace(ch) && newline) {
        newline = false;
      }
      buf.append(ch);
      i++;
    }
    return i;
  }

}
