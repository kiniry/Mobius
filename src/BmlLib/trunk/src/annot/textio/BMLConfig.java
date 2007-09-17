package annot.textio;

public class BMLConfig implements IDisplayStyle {

	private String indent = "";

	private AbstractPrettyPrinter prettyPrinter
		= IDisplayStyle.goUseSimplePrettyPrinter
		? new SimplePrettyPrinter(this)
		: new AdvancedPrettyPrinter(this);

	private boolean goControlPrint = false;

	private int root_pri;

	public BMLConfig() {}

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

	public boolean isGoControlPrint() {
		return goControlPrint;
	}

	public void setGoControlPrint(boolean goControlPrint) {
		this.goControlPrint = goControlPrint;
	}

	public String getIndent() {
		return indent;
	}

	public void setIndent(String indent) {
		this.indent = indent;
	}

	public AbstractPrettyPrinter getPrettyPrinter() {
		return prettyPrinter;
	}

	public int getRoot_pri() {
		return root_pri;
	}

	public void setRoot_pri(int root_pri) {
		this.root_pri = root_pri;
	}

}
