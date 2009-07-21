package annot.textio;

/**
 * This is the basic prettyPrinter, for use in case of problems
 * with main prettyPrinter ({@link AdvancedPrettyPrinter}).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class SimplePrettyPrinter extends AbstractPrettyPrinter {

  /**
   * A standard constructor.
   *
   * @param conf - current {@link BMLConfig}, should be
   *     avaliable as calling method argument.
   */
  public SimplePrettyPrinter(final BMLConfig conf) {
    super(conf);
  }

  /**
   * Adds a smartless line-breaking and constant indentation
   * to given String to make it little more readable.
   *
   * @param str - String representation of an expression
   *     to be formatted, wit hbocl marks.
   * @param spos - number of reserved characters for the
   *     first line.
   * @return <code>str</code> with simple line-breaking
   *     and indentation.
   * @see AbstractPrettyPrinter
   */
  @Override
  public String breakLines(final String str, final int spos) {
    String ret = "";
    final int width = DisplayStyle.MAX_TOTAL_LINE_WIDTH -
      getConf().newLine().length();
    String token = "";
    int pos = spos - DisplayStyle.LINE_INDENT_STRING.length();
    for (int i = 0; i  <  str.length(); i++) {
      final char ch = str.charAt(i);
      if (ch == DisplayStyle.BLOCK_EXPR_START) {
      } else if (ch == DisplayStyle.BLOCK_EXPR_END) {
        ret += token;
        token = "";
      } else if (pos  >  width) {
        ret += getConf().newLine();
        pos = token.length() + 1;
        token += ch;
      } else {
        pos++;
        token += ch;
      }
    }
    ret += token;
    return ret;
  }

}
