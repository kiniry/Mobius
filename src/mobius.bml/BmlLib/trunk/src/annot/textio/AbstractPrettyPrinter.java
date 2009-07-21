package annot.textio;

/**
 * Abstract class for all prettyPrinters. PrettyPrinters are
 * tools for line-breaking with proper indentation of an
 * expressions. This class contains also some methods that
 * can be useful for there its subclasses.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class AbstractPrettyPrinter {

  /**
   * @see BMLConfig
   */
  private final BMLConfig conf;

  /**
   * A standard constructor.
   *
   * @param aconf - current {@link BMLConfig}, should be
   *     available as calling method argument.
   */
  protected AbstractPrettyPrinter(final BMLConfig aconf) {
    this.conf = aconf;
  }

  /**
   * Correct formatting of annotation or whole bytecode,
   * using filters defined above. This method should be
   * called just before returning final String represntation
   * of class' bytecode.
   * Careful of changing this formatting, code search
   * mechanisms may stop working after some changes!
   *
   * @param astr - class' bytecode or it part (whole lines).
   * @return  <code>str</code> with corrected formatting.
   */
  public String afterDisplay(final String astr) {
    String str = astr;
    String result = "";
    str = filter3(str);
    final String[] lines = str.split("\n");
    for (int i = 0; i  <  lines.length; i++) {
      String s = lines[i];
      s = filter1(s);
      if (DisplayStyle.DISPLAY_RIGHT_MARGIN_MARKS) {
        s = filter2(s);
      }
      result += s + "\n";
    }
    return result;
  }

  /**
   * This method should add line-breaks and indentation to
   * given string to make it more readable. It should try
   * not produce lines larger than
   * {@link DisplayStyle#MAX_TOTAL_LINE_WIDTH}.
   *
   * @param str - String representation of an expression
   *     to be formatted. Each of it subexrpession should
   *     be, recursivly, surrounded by block marks from
   *     Idisplay interface. line-breaks should occure
   *     only just before or just after a block,
   * @param spos - number of reserved characters in first
   *     line (first line of the result must be
   *     <code>spos</code> characters shorter than maximum
   *     line width).
   * @return <code>str</code> with proper line-breaking
   *     and indentation.
   * @see DisplayStyle
   */
  public abstract String breakLines(String str, int spos);

  /**
   * Removes block marks from given String.
   *
   * @param str - String representation of an expression
   *     (or its part).
   * @return <code>str</code> with block marks removed.
   */
  public String cleanup(final String str) {
    String result = "";
    //XXX use regexp here
    for (int i = 0; i  <  str.length(); i++) {
      final char ch = str.charAt(i);
      if (ch != DisplayStyle.BLOCK_EXPR_START &&
          ch != DisplayStyle.BLOCK_EXPR_END) {
        result += ch;
      }
    }
    return result;
  }

  /**
   * Removes spaces from the end of given line.
   *
   * @param s - formatted (by prettyPrinter) single
   *     line String.
   * @return <code>s</code> with trailing spaces removed.
   */
  private String filter1(final String s) {
    if (DisplayStyle.BML_COMMENT_START.equals(s) ||
        DisplayStyle.BML_COMMENT_END_WITH_SPACES.equals(s)) {
      return s;
    }
    int i = s.length() - 1;
    while (i  >= 0 && s.charAt(i) == ' ') {
      i--;
    }
    if (i  <  0) {
      return "";
    }
    return s.substring(0, i + 1);
  }

  /**
   * Marks right margin in given line.
   *
   * @param astr - formatted (by prettyPrinter) single
   *     line String.
   * @return <code>s</code> with '|' character inserted
   *     after {@value DisplayStyle#MAX_TOTAL_LINE_WIDTH}'s
   *     character.
   */
  private String filter2(final String astr) {
    String s = astr;
    String result = "";
    s = s.replaceAll("\t", "        ");
    if (s.length()  <  DisplayStyle.MAX_TOTAL_LINE_WIDTH) {
      result = s;
      for (int i = s.length(); i  <  DisplayStyle.MAX_TOTAL_LINE_WIDTH; i++) {
        result += " ";
      }
      result += "|";
    } else {
      result = s.substring(0, DisplayStyle.MAX_TOTAL_LINE_WIDTH) + "|" +
        s.substring(DisplayStyle.MAX_TOTAL_LINE_WIDTH);
    }
    return result;
  }

  /**
   * Moves disallowed trailing characters
   * (such as '!', '~', '(') to the next line.
   *
   * @param s - formatted (by prettyPrinter) single
   *     line String.
   * @return <code>s</code> with disallowed trailing
   *     characters moved to the next line.
   */
  private String filter3(final String s) {
    final String[] ops = {"!", "~", "(" };
    String result = "";
    final String[] lines = s.split("\n");
    for (int i = 0; i  <  lines.length; i++) {
      String line = lines[i];
      if (!line.startsWith(DisplayStyle.BML_COMMENT_START) &&
          !line.startsWith(DisplayStyle.BML_COMMENT_NEXT)) {
        continue;
      }
      if (i == 0) {
        continue;
      }
      String prev = lines[i - 1];
      for (;;) {
        String suf = null;
        for (int o = 0; o  <  ops.length; o++) {
          if (prev.endsWith(ops[o])) {
            suf = ops[o];
          }
        }
        if (suf == null) {
          break;
        }
        for (int j = DisplayStyle.COMMENT_LENGTH; j  <  line.length(); j++) {
          if (line.charAt(j) != ' ') {
            final String l1 = line.substring(0, j);
            final String l2 = line.substring(j);
            line = l1 + prev.substring(prev.length() - suf.length()) + l2;
            prev = prev.substring(0, prev.length() - suf.length());
            break;
          }
        }
      }
      lines[i - 1] = prev;
      lines[i] = line;
    }
    for (int i = 0; i  <  lines.length; i++) {
      result += lines[i] + "\n";
    }
    return result;
  }

  /**
   * Removes last line from given String.
   *
   * @param str - multi line String.
   * @return <code>str</code> with last line removed.
   */
  protected String firstLines(final String str) {
    if (str.lastIndexOf("\n")  <  0) {
      return "";
    }
    return str.substring(0, str.lastIndexOf("\n") + 1);
  }

  /**
   * @return current display configuration.
   */
  protected BMLConfig getConf() {
    return this.conf;
  }

  /**
   * Removes all except last line from given String.
   *
   * @param str - multi line String.
   * @return last line of <code>str</code>.
   */
  protected String lastLine(final String str) {
    return str.substring(str.lastIndexOf("\n") + 1);
  }

  /**
   * Computes length of given string without block marks.
   *
   * @param str - String representation of an expression
   *     (or its part).
   * @return length of <code>str</code> (without block
   *     marks).
   */
  protected int strlen(final String str) {
    return cleanup(str).length();
  }

}
