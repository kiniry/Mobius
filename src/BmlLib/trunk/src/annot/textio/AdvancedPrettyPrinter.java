package annot.textio;

import java.util.Vector;

/**
 * This class is used for expression formatting
 * (with line-breaking and indentatoin).
 * 
 * @author tomekb
 */
public class AdvancedPrettyPrinter extends AbstractPrettyPrinter {

	/**
	 * Wether operators should be at the beginning (true)
	 * or end (false) of the line.
	 */
	private static final boolean startFromOp = false;

	/**
	 * A standard constructor.
	 * 
	 * @param conf - current {@link BMLConfig}, should be
	 * 		avaliable as calling method argument.
	 */
	public AdvancedPrettyPrinter(BMLConfig conf) {
		super(conf);
	}

	/**
	 * Divades current expression into subexpressions.
	 * Given expression is assumed to be an infix expression,
	 * with possible diffrent (even empty) operators
	 * between subexpressions.
	 * 
	 * @param str - String representation of an expression,
	 * 		without line breaking, but with block marks.
	 * 		Let <code>n</code> be the subexpression count
	 * 		of <code>str</code>.
	 * @return String array of <code>2*n+1</code> elements,
	 * 		starting from operator, containing operators at
	 * 		odd positions and subexpressions (with block marks)
	 * 		at even, and ending with operator. Order of these
	 * 		elements in returned array is the same as in given
	 * 		String.
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
		v.add(sub);
		String[] result = new String[v.size()];
		for (int i = 0; i < v.size(); i++)
			result[i] = v.elementAt(i);
		if (result.length < 5) {
			if (result.length < 2)
				return result;
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
	 * Formats given String.
	 * 
	 * @param prefix - single line prefix to be inserted
	 * 		before formatted expression,
	 * @param str - String representation of expression to be
	 * 		formatted (with block marks, but without
	 * 		line-breaks),
	 * @param suffix - single line suffix to be appended after
	 * 		formatted expression,
	 * @param indent - current indentation (used in the
	 * 		folowing lines by default).
	 * @return <code>prefix + str2 + suffix</code>, where
	 * 		<code>str2</code> is formatted <code>str</code>.
	 */
	private String bl(String prefix, String str, String suffix, String indent) {
		int width = IDisplayStyle.max_total_line_width
				- IDisplayStyle.comment_length;
		if (strlen(indent + prefix + str + suffix) < width)
			// str fits into current line
			return prefix + cleanup(str) + suffix;
		String[] sub = splitRoot(str);
		if (sub.length < 4)
			// str is a expression's leaf (no subexpressions)
			return prefix + cleanup(str) + suffix;
		String ret = "";
		boolean esinl = false; // each subexpression in new line
		int last = sub.length - 3;
		if (startFromOp) {
			for (int i = 0; i < sub.length - 2; i += 2) {
				String next = indent + sub[i] + sub[i + 1];
				if (i == 0)
					next = prefix + next;
				if (i == last)
					next += sub[i + 2] + suffix;
				if (strlen(next) > width) {
					esinl = true;
					break;
				}
			}
			String lp = prefix;
			for (int i = 0; i < sub.length - 2; i += 2) {
				String ind = indent + IDisplayStyle.lineIndent;
				String suf = "";
				if (i == last)
					suf = sub[i + 2] + suffix;
				if (i > 0) {
					String next = indent + lp + sub[i] + sub[i + 1] + suf;
					if (esinl || (strlen(next) > width)) {
						// new line
						ret += lp + "\n" + indent;
						if (cleanup(sub[i] + sub[i + 1]).charAt(0) != ' ')
							ret += ' '; // for operators not starting with spaces
						lp = "";
					}
				}
				lp += sub[i];
				String s1 = bl(lp, sub[i + 1], suf, ind);
				ret += firstLines(s1);
				lp = lastLine(s1);
			}
			ret += lp;
		} else {
			for (int i = 0; i < sub.length - 2; i += 2) {
				String next = indent + sub[i + 1] + sub[i + 2];
				if (i == 0)
					next = prefix + sub[i] + next;
				if (i == last)
					next += next + suffix;
				if (strlen(next) > width) {
					esinl = true;
					break;
				}
			}
			String lp = prefix + sub[0];
			for (int i = 0; i < sub.length - 2; i += 2) {
				String ind = indent + IDisplayStyle.lineIndent;
				String suf = "";
				if (i == last)
					suf += suffix;
				if (i > 0) {
					String next = indent + lp + sub[i + 1] + sub[i + 2] + suf;
					if (esinl || (strlen(next) > width)) {
						// new line
						ret += lp + "\n" + indent;
						if (cleanup(sub[i + 1]).charAt(0) != ' ')
							ret += ' ';
						lp = "";
					}
				}
				String s1 = bl(lp, sub[i + 1], sub[i + 2] + suf, ind);
				ret += firstLines(s1);
				lp = lastLine(s1);
			}
			ret += lp;
		}
		return ret;
	}

	/**
	 * @see AbstractPrettyPrinter#breakLines(String, int)
	 */
	@Override
	public String breakLines(String str, int spos) {
		String start = "";
		for (int i = 0; i < spos; i++)
			start += " ";
		String ret = bl(start, str, "", getConf().getIndent());
		ret = ret.substring(spos);
		return ret;
	}

}
