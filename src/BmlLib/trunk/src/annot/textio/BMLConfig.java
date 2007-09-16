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

}
