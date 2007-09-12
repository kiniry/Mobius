package annot.textio;

public abstract class AbstractPrettyPrinter {

	/**
	 * contains constants (e.g. line width) and environment (e.g. current
	 * indention) of expression to be formatted.
	 */
	protected BMLConfig conf;

	public abstract String afterDisplay(String str);

	public abstract String breakLines(String str, int spos);

	/**
	 * Removes blocks marks from given string.
	 * 
	 * @param str -
	 *            a String with BMLConfig.expr_block_start and
	 *            BMLConfig.expr_block_end characters.
	 * @return str without characters mentioned above.
	 */
	public String cleanup(String str) {
		String result = "";
		for (int i = 0; i < str.length(); i++) {
			char ch = str.charAt(i);
			if ((ch != IDisplayStyle.expr_block_start)
					&& (ch != IDisplayStyle.expr_block_end))
				result += ch;
		}
		return result;
	}

}
