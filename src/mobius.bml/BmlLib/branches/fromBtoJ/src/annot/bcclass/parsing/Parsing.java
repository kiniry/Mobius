package annot.bcclass.parsing;

import java.util.Iterator;

import org.antlr.runtime.ANTLRStringStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.attributes.AssertTable;
import annot.bcclass.attributes.BCAttribute;
import annot.bcclass.attributes.BCPrintableAttribute;
import annot.bcclass.attributes.LoopSpecification;

public class Parsing {
	private BCClass bcc;
	
	public Parsing(BCClass bcc) {
		this.bcc = bcc;
	}

	private BCPrintableAttribute getAttributeAtLine1(String str, int at) {
		String[] lines = str.split("\n");
		if (lines[at].length() == 0)
			return null;
		BCMethod m = null;
		for (int i=at; i>=0; i--) {
			String line = lines[i];
			if (line.matches("^[(public)|(protected)|(private)].*\\(.*\\)$")) {
				if (i == at)
					return null;
				Iterator iter = bcc.metody.iterator();
				while (iter.hasNext())
					if ((m=(BCMethod)(iter.next())).getHeader().equals(line))
						break;
				break;
			}
		}
		if (m == null)
			return null;
		int pc = -1;
		int n = 1;
		BCPrintableAttribute pa = null;
		int atype = 0; // 0 - null; 1 - assert; 2 - loop spec
		for (int i=at; i<lines.length; i++) {
			if (lines[i].matches("^[(public)|(protected)|(private)].*\\(.*\\)$"))
				break;
			if (lines[i].matches("^(\\d)+:.*$")) {
				pc = Integer.parseInt(lines[i].split(":")[0]);
				for (int j=at; j>=0; j--) {
					String line = lines[j];
					if (line.matches("^(\\d)+:.*$"))
						break;
					if ((atype == 0) || (atype == 1))
						if (line.matches(".*assert.*")) {
							AssertTable asst = m.getAssertTable();
							pa = asst.getAtPC(pc, n++);
							atype = 1;
						}
					if ((atype == 0) || (atype == 2))
						if (line.matches("^.*\\((\\d)+\\)$")) {
							LoopSpecification ls = m.getLoopSpecification();
							pa = ls.getAtPC(pc, n++);
							atype = 2;
						}
				}
				return pa;
			}
		}
		return m.getMethodSpecification();
	}

	/**
	 * Searches for an attribute in current class (bcc)
	 *  that has been printed at <code>at</code> line
	 *  of code <code>str</code> (using a printCode() method).
	 *  @param str - bytecode with annotations, generated
	 *  			 by this library, using <code>printCode()</code>
	 *  			 methods. Can be slightly modified before
	 *  			 calling this method.
	 *  @param at - position (line number) in <code>str</code>.
	 *  @return current (BML) attribute that should be located
	 *  	at given position in given bytecode (or null -- if
	 *  	no attributes are found there). The attribute isn't
	 *  	parsed here; an original representation is returned,
	 *  	even if attribute's text has been changed.
	 */
	public BCPrintableAttribute getAttributeAtLine(String str, int at) {
		BCPrintableAttribute ret = getAttributeAtLine1(str, at);
		if (ret == null)
			return null;
		String[] lines = str.split("\n");
		for (int i = at; i < lines.length; i++)
			if (lines[i].matches(".*\\*/.*")) {
				ret.line_end = i;
				break;
			}
		for (int i = at; i > 0; i--)
			if (lines[i].matches(".*/\\*.*")) {
				ret.line_start = i;
				break;
			}
		return ret;
	}
	
	public String getCurrentCode(BCPrintableAttribute pa, String str) {
		String ret = "";
		String[] lines = str.split("\n");
		for (int i=pa.line_start; i<=pa.line_end; i++)
			ret += lines[i] + "\n";
		return ret;
	}
	
	public String removeComment(String str) {
		String result = "";
		String[] lines = str.split("\n");
		for (int i=0; i<lines.length; i++)
			if (lines[i].length() > 3)
				result += lines[i].substring(3);
		result = result.split("\\*/")[0];
		return result;
	}

	public String purge(String attr) {
		attr = attr.replaceAll("/\\*", "");
		attr = attr.replaceAll("\\*/", "");
		attr = attr.replaceAll("\n \\*", "\n");
		attr = attr.replaceAll("\n", "");
		attr = attr.replaceAll(" ", "");
//		while (attr.lastIndexOf("  ") >= 0)
//			attr = attr.replaceAll("  ", " ");
		return attr;
	}
	
	public BCPrintableAttribute parseAttribute(BCMethod m, int pc, String str) throws RecognitionException {
		CharStream chstr = new ANTLRStringStream(str);
		BMLLexer lex = new BMLLexer(chstr);
		CommonTokenStream tokens = new CommonTokenStream(lex);
		BMLParser parser = new BMLParser(tokens);
		parser.init(m, pc);
		BCPrintableAttribute result = parser.printableAttribute().ast;
		if (lex.lastE != null)
			throw lex.lastE;
		if (parser.lastE != null)
			throw parser.lastE;
		return result;
	}

	public BCPrintableAttribute parseAttribute(BCPrintableAttribute oldattr, String str) throws RecognitionException {
		return parseAttribute(oldattr.method, oldattr.pcIndex, str);
	}
	
	public BCPrintableAttribute checkSyntax(BCPrintableAttribute oldattr, String str) {
		try {
			BCPrintableAttribute newattr = parseAttribute(oldattr.method, oldattr.pcIndex, str);
			newattr.line_start = oldattr.line_start;
			newattr.line_end = oldattr.line_end;
			return newattr;
		} catch (RecognitionException e) {
			return null;
		}
	}
}
