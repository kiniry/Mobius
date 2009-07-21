package annot.textio;

/**
 * This class represents current display configuration
 * and environment. Constant settings have been moved to
 * {@link DisplayStyle} interface. Objects of this class
 * should be transfered as one of the parameters for each
 * <code>printCode</code> methods for expressions, attributes,
 * methods, ...
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BMLConfig extends DisplayStyle {

  /**
   * Debug mode display, showing current expression AST.
   */
  private boolean goControlPrint;

  /**
   * Current indentation (for next line of code
   * or annotation).
   */
  private String indent = "";

  /**
   * Currently used prettyPrinter.
   */
  private final AbstractPrettyPrinter prettyPrinter =
    DisplayStyle.DISPLAY_USE_SIMPLE_PRETTYPRINTER ?
        new SimplePrettyPrinter(this) :
          new AdvancedPrettyPrinter(this);

  /**
   * Priority of the parent of currently displayed
   * expression.
   */
  private int root_pri;

  /**
   * A standard constructor.
   */
  public BMLConfig() {
  }

  /**
   * Decreases current indentation.
   */
  public void decInd() {
    this.indent = this.indent.substring(0, this.indent.length() -
                                        LINE_INDENT_STRING.length());
  }

  /**
   * @return current indentation.
   */
  public String getIndent() {
    return this.indent;
  }

  /**
   * @return Currently used prettyPrinter.
   */
  public AbstractPrettyPrinter getPrettyPrinter() {
    return this.prettyPrinter;
  }

  /**
   * @return Priority of parent expression. Outside
   *     exrpessions printCode(conf) method it may
   *     be undefined.
   */
  public int getRoot_pri() {
    return this.root_pri;
  }

  /**
   * Increases current indentation.
   */
  public void incInd() {
    this.indent += LINE_INDENT_STRING;
  }

  /**
   * @return {@link #goControlPrint} flag.
   */
  public boolean isGoControlPrint() {
    return this.goControlPrint;
  }

  /**
   * Use this instead of "\n" in <code>printCode(conf)</code>
   * methods.
   *
   * @return new line, with continue comment mark
   *     and indentation.
   */
  public String newLine() {
    return "\n" + BML_COMMENT_NEXT + this.indent;
  }

  /**
   * The same as {@link #newLine()}, bu with lesser
   * indentation.
   *
   * @see #newLine()
   * @return new line, with continue comment mark
   *     and lesser indentation.
   */
  public String nl() {
    decInd();
    final String str = newLine();
    incInd();
    return str;
  }

  /**
   * Sets {@link #goControlPrint} flag.
   *
   * @param agoControlPrint - flag value.
   */
  public void setGoControlPrint(final boolean agoControlPrint) {
    this.goControlPrint = agoControlPrint;
  }

  /**
   * Sets current indentation. This value will be used
   * from next displayed line (in next newline() call).
   *
   * @param aindent - new indentation value.
   */
  public void setIndent(final String aindent) {
    this.indent = aindent;
  }

  /**
   * Sets parent expression's priority. Use this before
   * recursive printCode(conf) call on subexpressions
   * (setting root_pri to current expression's priority).
   *
   * @param aroot_pri - priority value to be set.
   */
  public void setRoot_pri(final int aroot_pri) {
    this.root_pri = aroot_pri;
  }

}
