package annot.textio;

/**
 * This is the basic prettyPrinter, for use in case of problems
 * with main prettyPrinter ({@link AdvancedPrettyPrinter}).
 * 
 * @author tomekb
 */
public class SimplePrettyPrinter extends AbstractPrettyPrinter {

	/**
	 * A standard constructor.
	 * 
	 * @param conf - current {@link BMLConfig}, should be
	 * 		avaliable as calling method argument.
	 */
	public SimplePrettyPrinter(BMLConfig conf) {
		super(conf);
	}

	/**
	 * Adds a smartless line-breaking and constant indentation
	 * to given String to make it little more readable.
	 * 
	 * @param str - String representation of an expression
	 * 		to be formatted, wit hbocl marks.
	 * @param spos - number of reserved characters for the
	 * 		first line.
	 * @return <code>str</code> with simple line-breaking
	 * 		and indentation.
	 * @see AbstractPrettyPrinter
	 */
	@Override
	public String breakLines(String str, int spos) {
		String ret = "";
		int width = IDisplayStyle.max_total_line_width
				- getConf().newLine().length();
		String token = "";
		int pos = spos - IDisplayStyle.lineIndent.length();
		for (int i = 0; i < str.length(); i++) {
			char ch = str.charAt(i);
			if (ch == IDisplayStyle.expr_block_start) {
			} else if (ch == IDisplayStyle.expr_block_end) {
				ret += token;
				token = "";
			} else if (pos > width) {
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
