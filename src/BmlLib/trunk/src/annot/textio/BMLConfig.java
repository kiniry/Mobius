package annot.textio;

/**
 * This class represents current display configuration
 * and environment. Constant settings have been moved to
 * {@link IDisplayStyle} interface. Objects of this class
 * should be transfered as one of the parameters for each
 * <code>printCode</code> methods for expressions, attributes,
 * methods, ...
 * 
 * @author tomekb
 */
public class BMLConfig implements IDisplayStyle {

	/**
	 * Current indentation (for next line of code
	 * or annotation).
	 */
	private String indent = "";

	/**
	 * Currently used prettyPrinter.
	 */
	private AbstractPrettyPrinter prettyPrinter
			= IDisplayStyle.goUseSimplePrettyPrinter
			? new SimplePrettyPrinter(this)
			: new AdvancedPrettyPrinter(this);

	/**
	 * Debug mode display, showing current expression AST.
	 */
	private boolean goControlPrint = false;

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
	 * Use this instead of "\n" in <code>printCode(conf)</code>
	 * methods.
	 * 
	 * @return new line, with continue comment mark
	 * 		and indentation.
	 */
	public String newLine() {
		return "\n" + comment_next + indent;
	}

	/**
	 * The same as {@link #newLine()}, bu with lesser
	 * indentation.
	 *
	 * @see #newLine()
	 * @return new line, with continue comment mark
	 * 		and lesser indentation.
	 */
	public String nl() {
		decInd();
		String str = newLine();
		incInd();
		return str;
	}

	/**
	 * Increases current indentation.
	 */
	public void incInd() {
		indent += lineIndent;
	}

	/**
	 * Decreases current indentation.
	 */
	public void decInd() {
		indent = indent.substring(0, indent.length() - lineIndent.length());
	}

	/**
	 * @return {@link #goControlPrint} flag.
	 */
	public boolean isGoControlPrint() {
		return goControlPrint;
	}

	/**
	 * Sets {@link #goControlPrint} flag.
	 * 
	 * @param goControlPrint - flag value.
	 */
	public void setGoControlPrint(boolean goControlPrint) {
		this.goControlPrint = goControlPrint;
	}

	/**
	 * @return current indentation.
	 */
	public String getIndent() {
		return indent;
	}

	/**
	 * Sets current indentation. This value will be used
	 * from next displayed line (in next newline() call).
	 * 
	 * @param indent - new indentation value.
	 */
	public void setIndent(String indent) {
		this.indent = indent;
	}

	/**
	 * @return Currently used prettyPrinter.
	 */
	public AbstractPrettyPrinter getPrettyPrinter() {
		return prettyPrinter;
	}

	/**
	 * @return Priority of parent expression. Outside
	 * 		exrpessions printCode(conf) method it may
	 * 		be undefined.
	 */
	public int getRoot_pri() {
		return root_pri;
	}

	/**
	 * Sets parent expression's priority. Use this before
	 * recursive printCode(conf) call on subexpressions
	 * (setting root_pri to current expression's priority). 
	 * 
	 * @param root_pri - priority value to be set.
	 */
	public void setRoot_pri(int root_pri) {
		this.root_pri = root_pri;
	}

}
