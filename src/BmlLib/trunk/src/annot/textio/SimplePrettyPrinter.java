package annot.textio;

public class SimplePrettyPrinter extends AbstractPrettyPrinter {
	
	public SimplePrettyPrinter(BMLConfig conf) {
		super(conf);
	}

	@Override
	public String breakLines(String str, int spos) {
		String ret = "";
		int width = IDisplayStyle.max_total_line_width
		- getConf().newLine().length();
		String token = "";
		int pos = spos - IDisplayStyle.lineIndent.length();
		for (int i=0; i<str.length(); i++) {
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
