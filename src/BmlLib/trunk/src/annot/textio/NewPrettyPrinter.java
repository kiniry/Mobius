package annot.textio;

public class NewPrettyPrinter extends PrettyPrinter {
	// ERRORS!

	private int maxW;

	public NewPrettyPrinter(BMLConfig conf) {
		super(conf);
		maxW = IDisplayStyle.max_total_line_width - conf.indent.length()
				- IDisplayStyle.comment_next.length();
	}

	private String firstLines(String str) {
		if (str.lastIndexOf("\n") < 0)
			return "";
		return str.substring(0, str.lastIndexOf("\n") + 1);
	}

	private String lastLine(String str) {
		return str.substring(str.lastIndexOf("\n") + 1);
	}

	private String indent(String code, int n) {
		if (code.indexOf("\n") < 0)
			return code;
		String[] lines = code.split("\n");
		String ret = "";
		for (int i = 0; i < lines.length; i++) {
			if (i > 0)
				ret += "\n";
			ret += IDisplayStyle.comment_next;
			if (i >= n)
				ret += IDisplayStyle.lineIndent;
			ret += lines[i].substring(IDisplayStyle.comment_next.length());
		}
		return ret;
	}

	private String bl(String prefix, String input, String suffix) {
		if (input.length() == 0)
			return "";
		if (strlen(prefix + input + suffix) < maxW) {
			return prefix + cleanup(input) + suffix; // if whole expression fit
			// into current line
		}
		String[] sub = splitRoot(input);
		if (sub.length <= 2) // if we are in leaf of the expression
			return prefix + conf.newLine() + cleanup(sub[0]) + suffix;
		int maxi = sub.length;
		maxi -= 4;
		suffix = sub[sub.length - 2] + suffix;
		// ( x + y + z ) _
		// 0 1 2 3 4 5 6 7
		int n = 1;
		String output = prefix; // returned String
		if (startFormOp) {
			if (!conf.newLine().equals("\n" + prefix))
				if (strlen(prefix + sub[0] + sub[1] + suffix) >= maxW) {
					output += conf.newLine();
					n = 2;
				}
			for (int i = 0; i <= maxi; i += 2) {
				boolean lastSub = i == maxi;
				String str = bl(lastLine(output), sub[i] + sub[i + 1],
						lastSub ? suffix : "");
				output = firstLines(output) + str;
			}
		} else {
			// TODO
		}
		return indent(output, n);
		// return output;
	}

	@Override
	public String breakLines(String str, int spos) {
		String prefix = "";
		for (int i = 0; i < spos; i++)
			prefix += " ";
		conf.decInd();// ?
		String ret = bl(prefix, str, "");
		// ret = indent(ret, 0);
		conf.incInd();// ?
		ret = ret.substring(spos);
		return ret;
	}

}
