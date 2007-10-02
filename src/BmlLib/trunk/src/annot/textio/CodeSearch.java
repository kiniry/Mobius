package annot.textio;

import annot.attributes.AType;
import annot.attributes.BCPrintableAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;

/**
 * This ugly class searches for BML annotations in bytecode.
 * 
 * @author tomekb
 */
@Deprecated
public final class CodeSearch {

	/**
	 * @return array of all keywords.
	 */
	public static String[] getAllAttributeNames() {
		String[] ret = { IDisplayStyle._classInvariant,
				IDisplayStyle._requires, IDisplayStyle._precondition,
				IDisplayStyle._postcondition, IDisplayStyle._assert };
		return ret;
	}

	/**
	 * Returns type of given line.
	 * 
	 * @param line - single line String.
	 * @return <b>"EOC"</b> - for end of comment only,<br>
	 * 		<b>"method"</b> - for method declaration,<br>
	 * 		<b>pc number</b> - for instruction line, <br>
	 * 		<b>annotation keyword</b> - for first annotation's
	 * 			line,<br>
	 * 		<b>""</b> - for other line types.
	 */
	public static String getKeyword(String line) {
		if (line.startsWith(IDisplayStyle.comment_start)) {
			line = line.substring(IDisplayStyle.comment_start.length());
		} else if (line.startsWith(IDisplayStyle.comment_next)) {
			line = line.substring(IDisplayStyle.comment_next.length());
		} else if (line.startsWith(IDisplayStyle.comment_end)) {
			return "EOC";
		} else if (line.startsWith("public") || (line.startsWith("protected"))
				|| line.startsWith("private")) {
			return "method";
		} else {
			int i = line.indexOf(":");
			if ((i < 0) || (i > 5))
				return "";
			return line.substring(0, i);
		}
		String[] all = getAllAttributeNames();
		for (int i = 0; i < all.length; i++)
			if (line.startsWith(all[i]))
				return all[i];
		if (line.length() == 0)
			return "";
		while (line.charAt(0) == ' ') {
			if (line.length() < 2)
				return "";
			line = line.substring(1);
		}
		int p = line.indexOf(' ');
		if (p < 0)
			return "";
		return line.substring(0, p);
	}

	/**
	 * Checks if given String in a annotation keyword.
	 * 
	 * @param str - String to check.
	 * @return wether <code>str</code> is a annotation
	 * 		keyword or not.
	 */
	public static boolean isAttributeStr(String str) {
		String[] all = getAllAttributeNames();
		for (int i = 0; i < all.length; i++)
			if (all[i].equals(str))
				return true;
		return false;
	}

	/**
	 * Checks if given String represents a natural number.
	 * 
	 * @param str - String to check.
	 * @return wether <code>str</code> is a String
	 * 		representation of number or not.
	 */
	public static boolean isNumber(String str) {
		return str.matches("^\\-?[0-9]+");
	}

	/**
	 * Computes annotation position of given line.
	 * 
	 * @param code - whole class' bytecode, formatted and
	 * 		with annotations.
	 * @param line - line number in <code>code</code>,
	 * 		starting from 0.
	 * @return an integer array describing this line's
	 * 		position with:<br>
	 * 		<b>method</b> number (index used eg. in
	 * 		{@link BCClass#getMethod(int)}),<br>
	 * 		<b>pc</b> number (offset) of bytecode
	 * 		instruction,<br>
	 * 		<b>minor</b> number of this annotation,<br>
	 * 		<b>length</b> of this annotation (in lines).<br>
	 * 		Returns <b>null</b> if there are no BML
	 * 		annotations at given line in <code>code</code>.
	 */
	public static int[] where(String code, int line) {
		int[] ret = { -1, -1, -1, -2 };
		String[] lines = code.split("\n");
		String[] codes = new String[lines.length];
		for (int i = 0; i < lines.length; i++)
			codes[i] = getKeyword(lines[i]);
		if (!isAttributeStr(codes[line]))
			return null;
		for (int i = line + 1; i < lines.length; i++)
			if (!"".equals(codes[i])) {
				ret[3] = i - 1 - line;
				break;
			}
		if (lines[line].indexOf(IDisplayStyle.comment_end) >= 0)
			ret[3] = 0;
		for (int i = 0; i < line; i++) {
			if ("method".equals(codes[i])) {
				ret[0]++;
				ret[2] = -1;
			} else if (isNumber(codes[i])) {
				ret[2] = 0;
			} else if (isAttributeStr(codes[i])) {
				ret[2]++;
			}
		}
		for (int i = line; i < codes.length; i++)
			if (isNumber(codes[i])) {
				ret[1] = Integer.parseInt(codes[i]);
				break;
			}
		return ret;
	}

	/**
	 * Searches for attribute from given class that
	 * is displayed at given line of given code.
	 * 
	 * @param bcc - BCClass to search in,
	 * @param code - String representation of bytecode from
	 * 		that class, recived using
	 * 		<code>bcc.printCode()</code> method.
	 * @param line - line number in given code,
	 * 		starting from 0.
	 * @return Annotation from <code>bcc</code> that has been
	 * 		diaplayed at <code>line</code> line of
	 * 		<code>code</code>, or null if no such annotation
	 * 		could be found in <code>bcc</code>.
	 */
	public static BCPrintableAttribute findAttributeAtLine(BCClass bcc,
			String code, int line) {
		int[] w = where(code, line);
		if (w == null)
			return null;
		String type = getKeyword(code.split("\n")[line]);
		if (IDisplayStyle._classInvariant.equals(type))
			return bcc.getInvariant();
		if (IDisplayStyle._requires.equals(type))
			return bcc.getMethod(w[0]).getMspec();
		if (IDisplayStyle._assert.equals(type)) {
			BCMethod m = bcc.getMethod(w[0]);
			return m.getAmap().getAllAt(m.findAtPC(w[1])).getAll(AType.C_ALL)[w[2]];
		}
		return null;
	}

	/**
	 * Replace all characters (except newlines) of given
	 * String with 'X' characters.
	 * 
	 * @param str - multi line String.
	 * @return <code>str</code> with all except '\n' characters
	 * 		replaced with 'X'.
	 */
	private static String clear(String str) {
		String ret = "";
		for (int i = 0; i < str.length(); i++) {
			char ch = str.charAt(i);
			if (ch == '\n') {
				ret += '\n';
			} else {
				ret += 'X';
			}
		}
		return ret;
	}

	/**
	 * Compute line numbers of lines in whitch they were
	 * displayed for each annotation in given BCClass.
	 * 
	 * @param bcc - BCClass to update.
	 */
	public static void ComputeAttributeLines(BCClass bcc) {
		BMLConfig conf = new BMLConfig();
		BCPrintableAttribute[] all = bcc.getAllAttributes(AType.C_ALL);
		String code = bcc.printCode();
		code = Parsing.removeComment(code);
		// MLog.putMsg(MLog.PDebug, code);
		for (int a = 0; a < all.length; a++) {
			String lc = all[a].getLast_code();
			lc = Parsing.addComment(lc);
			lc = conf.getPrettyPrinter().afterDisplay(lc);
			lc = Parsing.removeComment(lc);
			// MLog.putMsg(MLog.PDebug, "#"+lc+"#");
			if (lc.length() == 0)
				throw new RuntimeException("attribute wasn't displayed yet!");
			int pos = code.indexOf(lc);
			if (pos < 0) {
				System.out.println(all[a].getLast_code());
				System.out.println(lc);
				System.out.println(code);
				throw new RuntimeException("attribute's code not found!");
			}
			code = code.substring(0, pos) + clear(lc)
					+ code.substring(pos + lc.length());
			int pos2 = pos + lc.length();
			while (code.charAt(pos) == '\n')
				pos++;
			while (code.charAt(pos2) == '\n')
				pos2--;
			int start = Parsing.lineAt(code, pos + 1);
			int end = Parsing.lineAt(code, pos2);
			MLog.putMsg(MLog.PNotice, a + ": " + start + "--" + end);
			all[a].line_start = start;
			all[a].line_end = end;
		}
	}

}
