package annot.textio;

import java.util.Vector;

public class PrettyPrinter extends AbstractPrettyPrinter {

	/**
	 * true iff infix operators should be at the beginning of a line.
	 */
	public boolean startFormOp = true;

	public PrettyPrinter(BMLConfig conf) {
		this.conf = conf;
	}

	/**
	 * Adds vertical line after screen width (conf.max_total_line_width) column.
	 * 
	 * @param s -
	 *            string (single line, without \n) to be processed
	 * @return s with "|" inserted after screen width's column
	 */
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

	/**
	 * Removes trailing spaces from given line.
	 * 
	 * @param s -
	 *            string (single line, without \n) to be processed
	 * @return s with trailing spaces removed.
	 */
	private String filter1(String s) {
		int i = s.length() - 1;
		while ((i >= 0) && (s.charAt(i) == ' '))
			i--;
		if (i < 0)
			return "";
		return s.substring(0, i + 1);
	}

	/**
	 * Applies some filters for each line of generated code, to improve it's
	 * look. Should be called after generating code.
	 */
	@Override
	public String afterDisplay(String str) {
		String result = "";
		String[] lines = str.split("\n");
		for (int i = 0; i < lines.length; i++) {
			String s = lines[i];
			s = filter1(s);
			// s = filter2(s);
			result += s + "\n";
		}
		return result;
	}

	/**
	 * splits given expression into subexpressions.
	 * 
	 * @param str -
	 *            string representation of expression, with infix blocks marked
	 *            using constants in BMLConfig, and without line breaks.
	 * @return String array of infix operators on even positions, and following
	 *         subexpressions on odd positions. Last element is an empty string,
	 *         to avoid ArrayIndexOutOfBounds errors.
	 */
	protected String[] splitRoot(String str) {
		Vector<String> v = new Vector<String>();
		int level = 0;
		String sub = "";
		for (int p = 0; p < str.length(); p++) {
			char ch = str.charAt(p);
			if (ch == IDisplayStyle.expr_block_start) {
				if (level == 0) {
					v.add(sub);
					sub = "";
				} else {
					sub += IDisplayStyle.expr_block_start;
				}
				level++;
			} else if (ch == IDisplayStyle.expr_block_end) {
				level--;
				if (level < 0)
					throw new RuntimeException(str.substring(0, p) + "#"
							+ str.substring(p));
				if (level == 0) {
					v.add(sub);
					sub = "";
				} else {
					sub += IDisplayStyle.expr_block_end;
				}
			} else {
				sub += ch;
			}
		}
		// if ((v.size() == 0) &&
		// (str.lastIndexOf(IDisplayStyle.expr_block_start) >= 0))
		// return (splitRoot(str.substring(1, str.length()-1)));
		v.add(sub);
		v.add("");
		String[] result = new String[v.size()];
		for (int i = 0; i < v.size(); i++)
			result[i] = v.elementAt(i);
		if (result.length < 5) {
			if (result[1].indexOf(IDisplayStyle.expr_block_start) < 0)
				return result;
			String[] nr = splitRoot(result[1]);
			nr[0] = result[0] + nr[0];
			nr[nr.length - 2] += result[2];
			return nr;
		}
		return result;
	}

	/**
	 * Computes length of a string, without block marks.
	 * 
	 * @param str -
	 *            a String with blocks marked as in procedures above.
	 * @return length of str without block marks.
	 */
	protected int strlen(String str) {
		return cleanup(str).length();
	}

	/**
	 * Insert line-breaks and indentations to given String.
	 * 
	 * @param str -
	 *            String representation of an expression with blocks marked with
	 *            BMLConfig.expr_block_start and BMLConfig.expr_block_end and
	 *            without newLines ("\n")
	 * @param start -
	 *            used characters in current line, excluding standard
	 *            indentation
	 * @param end -
	 *            used characters at the end of last generated lines (used only
	 *            iff <code>startFromOp</code> == false)
	 * @param w -
	 *            indentation to be used at the root of expression
	 *            <code>str</code>.
	 * @param prefix -
	 *            operator to be inserted after newLine (used only if
	 *            <code>startFromOp</code> == true).
	 * @return <code>str</code> with line-breaks and indentation when
	 *         nessesery. No line of this expression should be longer than
	 *         max_total_line_width defined in BMLConfig (if possible). The
	 *         first line should be shorter by at least <code>start</code>
	 *         lines, and the last line by <code>end</code> lines.
	 */
	private String breakLines(String str, int start, int end, String w,
			String prefix) {
		// start variable is used as current position (after indent) in line
		// inside this procedure
		if (str.length() == 0)
			return "";
		String result = ""; // returned String
		if (conf.start_line_pos() + start + strlen(str) < IDisplayStyle.max_total_line_width
				- end) {
			return cleanup(str); // if whole expression fit into current line
		}
		String[] sub = splitRoot(str);
		if (sub.length <= 2) // if we are in leaf of the expression
			return prefix + cleanup(sub[0]);
		String oldInd = conf.indent;
		conf.indent = w; // increase indentation to w (for next lines)
		boolean ok = true; // iff all subexpr. can be displayed in one line
		if (startFormOp) {
			for (int i = 0; i < sub.length - 1; i += 2) { // for each
				// subexpression
				// with its operator
				int epos = 0; // unused? 'end' parameter should be always zero
				// in this case (startFromOp == true)
				String s = sub[i] + sub[i + 1]; // current (operator +
				// subexpression)
				if ((conf.start_line_pos() + start + strlen(s) <= IDisplayStyle.max_total_line_width
						- epos)
						&& ok) {
					// s fit into current line
					// and we are allowed to display subexpression in the same
					// line (ok == true)
					result += cleanup(s);
					start += strlen(s);
				} else {
					String[] sub2 = splitRoot(sub[i + 1]); // subexpressions of
					// current
					// subexpression
					boolean b = false; // first subexpression of current
					// subexpression won't fit into current
					// line
					if (sub2.length > 3)
						b = breakLines(sub2[1], strlen(sub[i] + prefix), epos,
								w + IDisplayStyle.lineIndent, "").lastIndexOf(
								"\n") >= 0;
					// indentation won't extend if it will do so just after, in
					// recursive call, before writing
					// anything, to avoid double indentation after quantifiers,
					// for example.
					// FIXME! double indentations should be removed in
					// afterDisplay()
					String e = breakLines(sub[i + 1], strlen(sub[i] + prefix),
							epos, b ? w : w + IDisplayStyle.lineIndent,
							(b ? prefix : "") + sub[i]);
					// e is the string representation of current subexpression,
					// with preceding operator (sub[i]),
					// displayed with line breaking and indentation.
					if (e.length() == 0) {
						// for operators that are after last subexpressions,
						// e.g. sub[i]=="]" in array[index]
						result += sub[i];
						continue;
					}
					if (e.charAt(0) != '\n') {
						// adding newline unless we did it at the beginning of
						// recursive call.
						result += conf.newLine();
						if (i < 2) // if it's the first subexpression, we
							// should add prefix just after newline
							result += prefix;
						start = 0; // reseting current position to beginning of
						// the line
						if (e.substring(1).lastIndexOf('\n') >= 0)
							ok = false; // next subexpressions at this level
						// will be displayed in separate lines.
						result += sub[i]; // writing operator
					} // {else // operator has been already written (to e) in
					// recursive call, as a 'prefix' argument}
					result += e; // writing current subexpression
					start += result.length() - (result.lastIndexOf("\n") + 1)
							- conf.start_line_pos(); // updating position in
					// current line
				}
				prefix = "";
			}
		} else { // this case is very similar to the previous one.
			// in this case, 'prefix' argument will be unused
			result += sub[0]; // writing first (prefix) operator, if any
			start += strlen(sub[0]); // and updating position
			for (int i = 1; i < sub.length - 1; i += 2) {
				// if this is the last subexpression, we have to left some
				// ('end' argument)
				// space at the end of the line for parent's operator
				int epos = (i > sub.length - 4) ? end : 0;
				String s = sub[i] + sub[i + 1]; // current (subexpression +
				// operator)
				if ((conf.start_line_pos() + start + strlen(s) <= IDisplayStyle.max_total_line_width
						- epos)
						&& ok) {
					result += cleanup(s);
					start += strlen(s);
				} else {
					String[] sub2 = splitRoot(sub[i]);
					boolean b = false;
					if (sub2.length > 3)
						b = breakLines(sub2[1], 0, sub2[2].length() + epos,
								w + IDisplayStyle.lineIndent, "").lastIndexOf(
								"\n") >= 0;
					String e = breakLines(sub[i], 0,
							sub[i + 1].length() + epos, b ? w : w
									+ IDisplayStyle.lineIndent, "");
					if ((e.charAt(0) != '\n') && (i > 1)) {
						result += conf.newLine();
						start = 0;
						if (e.substring(1).lastIndexOf("\n") >= 0)
							ok = false;
					}
					result += e + sub[i + 1];
					start += result.length() - (result.lastIndexOf("\n") + 1)
							- conf.start_line_pos();
				}
			}
		}
		conf.indent = oldInd; // restoring indentation
		return result;
	}

	/**
	 * Adds line-breaking with indentation to str (first line should be shorter
	 * by <code>spos</code> characters).
	 */
	@Override
	public String breakLines(String str, int spos) {
		return breakLines(str, spos, 0, conf.indent, "");
	}

}
