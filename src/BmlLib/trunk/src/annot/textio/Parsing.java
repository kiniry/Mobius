package annot.textio;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.attributes.BCPrintableAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;

public class Parsing {

	private BCClass bcc;

	public Parsing(BCClass bcc) {
		this.bcc = bcc;
	}

	public static int lineAt(String code, int pos) {
		return code.substring(0, pos).split("\n").length - 1;
	}

	public static String getLines(String code, int start, int end) {
		String ret = "";
		String[] lines = code.split("\n");
		for (int i = start; i <= end; i++)
			ret += lines[i];
		return ret;
	}

	public static String escape(String str) {
		str = str.replaceAll("\\\\", "\\\\\\\\");
		str = str.replaceAll("\\*", "\\\\\\*");
		str = str.replaceAll("\\{", "\\\\\\{");
		str = str.replaceAll("\\}", "\\\\\\}");
		return str;
	}

	public static String removeComment(String attr) {
		attr = attr.replaceAll(escape(IDisplayStyle.comment_start), "");
		attr = attr.replaceAll(escape("\n" + IDisplayStyle.comment_next), "\n");
		attr = attr.replaceAll(escape(IDisplayStyle.comment_end), "");
		return attr;
	}

	public static String purge(String attr) {
		attr = removeComment(attr);
		attr = attr.replaceAll("\n", "");
		while (attr.lastIndexOf("  ") >= 0)
			attr = attr.replaceAll("  ", " ");
		return attr;
	}

	public static String addComment(String code) {
		if (code.length() < 1)
			return "";
		if (code.lastIndexOf("\n") == code.length() - 1)
			code = code.substring(0, code.length() - 1);
		if ((code.lastIndexOf("\n") >= 0)
				|| (code.length() > IDisplayStyle.max_total_line_width
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

	public BCPrintableAttribute parseAttribute(BCMethod m,
			InstructionHandle ih, int minor, String str)
			throws RecognitionException {
		CharStream chstr = new ANTLRStringStream(str);
		BMLLexer lex = new BMLLexer(chstr);
		CommonTokenStream tokens = new CommonTokenStream(lex);
		BMLParser parser = new BMLParser(tokens);
		parser.init(bcc, m, bcc.getCp(), ih, minor);
		BCPrintableAttribute result = parser.printableAttribute().ast;
		if (lex.lastE != null)
			throw lex.lastE;
		if (parser.lastE != null)
			throw parser.lastE;
		return result;
	}

	public BCPrintableAttribute checkSyntax(BCMethod m,
			InstructionHandle ih, int minor, String str) {
		try {
			BCPrintableAttribute newattr = parseAttribute(m, ih, minor,
					str);
			return newattr;
		} catch (RecognitionException e) {
			return null;
		}
	}

}
