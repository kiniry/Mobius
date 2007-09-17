package annot.textio;

public abstract class AbstractPrettyPrinter {

	private BMLConfig conf;

	protected AbstractPrettyPrinter(BMLConfig conf) {
		this.conf = conf;
	}
	
	public abstract String breakLines(String str, int spos);

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

	protected int strlen(String str) {
		return cleanup(str).length();
	}
	
	private String filter1(String s) {
		if ((IDisplayStyle.comment_start.equals(s))
			|| (IDisplayStyle.comment_end.equals(s)))
				return s;
		int i = s.length() - 1;
		while ((i >= 0) && (s.charAt(i) == ' '))
			i--;
		if (i < 0)
			return "";
		return s.substring(0, i + 1);
	}

	private String filter2(String s) {
		String result = "";
		s = s.replaceAll("\t", "        ");
		if (s.length() < IDisplayStyle.max_total_line_width) {
			result = s;
			for (int i = s.length(); i < IDisplayStyle.max_total_line_width; i++)
				result += " ";
			result += "|";
		} else {
			result = s.substring(0, IDisplayStyle.max_total_line_width) + "|"
					+ s.substring(IDisplayStyle.max_total_line_width);
		}
		return result;
	}

	private String filter3(String s) {
		String[] ops = {"!", "~", "("};
		String result = "";
		String[] lines = s.split("\n");
		for (int i=0; i<lines.length; i++) {
			String line = lines[i];
			if ((!line.startsWith(IDisplayStyle.comment_start))
				&& (!line.startsWith(IDisplayStyle.comment_next)))
				continue;
			if (i == 0)
					continue;
			String prev = lines[i-1];
			for(;;) {
				String suf = null;
				for (int o=0; o<ops.length; o++)
					if (prev.endsWith(ops[o]))
						suf = ops[o];
				if (suf == null)
					break;
				for (int j=IDisplayStyle.comment_length; j<line.length(); j++)
					if (line.charAt(j) != ' ') {
						String l1 = line.substring(0, j);
						String l2 = line.substring(j);
						line = l1 + prev.substring(
								prev.length() - suf.length())
								+ l2;
						prev = prev.substring(0,
								prev.length() - suf.length());
						break;
					}
			}
			lines[i-1] = prev;
			lines[i] = line;
		}
		for (int i=0; i<lines.length; i++)
			result += lines[i] + "\n";
		return result;
	}
	
	public String afterDisplay(String str) {
		String result = "";
		str = filter3(str);
		String[] lines = str.split("\n");
		for (int i = 0; i < lines.length; i++) {
			String s = lines[i];
			s = filter1(s);
			if (IDisplayStyle.goShowRightMargin)
				s = filter2(s);
			result += s + "\n";
		}
		return result;
	}

	protected String firstLines(String str) {
		if (str.lastIndexOf("\n") < 0)
			return "";
		return str.substring(0, str.lastIndexOf("\n") + 1);
	}

	protected String lastLine(String str) {
		return str.substring(str.lastIndexOf("\n") + 1);
	}

	protected BMLConfig getConf() {
		return conf;
	}

}
