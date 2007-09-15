package annot.textio;

public class BMLConfig implements IDisplayStyle {

	public String indent = "";

	public AbstractPrettyPrinter prittyPrinter = new NewPrettyPrinter1(this);

	public boolean goControlPrint = false;

	public int root_pri;

	public BMLConfig() {
	}

	public String newLine() {
		return "\n" + comment_next + indent;
	}

	public int start_line_pos() {
		return newLine().length() - 1;
	}

	public void incInd() {
		indent += lineIndent;
	}

	public void decInd() {
		indent = indent.substring(0, indent.length() - lineIndent.length());
	}

	public String addComment(String code) {
		if (code.length() < 1)
			return "";
		if (code.lastIndexOf("\n") == code.length() - 1)
			code = code.substring(0, code.length() - 1);
		if ((code.lastIndexOf("\n") >= 0)
				|| (code.length() > max_total_line_width
						- IDisplayStyle.comment_start.length()
						- IDisplayStyle.comment_end.length())) {
			String[] lines = code.split("\n");
			code = "";
			for (int i = 0; i < lines.length; i++) {
				if (!lines[i].startsWith(IDisplayStyle.comment_next))
					lines[i] = IDisplayStyle.comment_next + lines[i];
				if (lines[i].equals(IDisplayStyle.comment_next))
					continue;
				code += lines[i] + "\n";
			}
			return IDisplayStyle.comment_start + "\n" + code
					+ IDisplayStyle.comment_end + "\n";
		} else {
			return IDisplayStyle.comment_start + code
					+ IDisplayStyle.comment_end + "\n";
		}
	}

}
