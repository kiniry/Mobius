package annot.textio;

import java.util.Vector;

public class NewPrettyPrinter1 extends AbstractPrettyPrinter {

	private static final boolean startFromOp = false;
	
	public NewPrettyPrinter1(BMLConfig conf) {
		super(conf);
	}

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

	private String bl(String prefix, String str, String suffix, String indent) {
		int width = IDisplayStyle.max_total_line_width - IDisplayStyle.comment_length;
		if (strlen(indent+prefix+str+suffix) < width)
			return prefix+cleanup(str)+suffix;
		String[] sub = splitRoot(str);
		if (sub.length < 4)
			return prefix+cleanup(str)+suffix;
		String ret = "";
		boolean esinl = false; // each subexpression in new line
		int last = sub.length-3;
		if (startFromOp) {
			for (int i=0; i<sub.length-2; i+=2) {
				String next = indent + sub[i] + sub[i+1];
				if (i == 0)
					next = prefix + next;
				if (i == last)
					next += sub[i+2] + suffix;
				if (strlen(next) > width) {
					esinl = true;
					break;
				}
			}
			String lp = prefix;
			for (int i=0; i<sub.length-2; i+=2) {
				String ind = indent + IDisplayStyle.lineIndent;
				String suf = "";
				if (i == last)
					suf = sub[i+2] + suffix;
				if (i > 0) {
					String next = indent + lp + sub[i] + sub[i+1] + suf;
					if (esinl || (strlen(next) > width)) {
						//new line
						ret += lp + "\n" + indent;
						if (cleanup(sub[i] + sub[i+1]).charAt(0) != ' ')
							ret += ' ';
						lp = "";
					}
				}
				lp += sub[i];
				String s1 = bl(lp, sub[i+1], suf, ind);
				ret += firstLines(s1);
				lp = lastLine(s1);
			}
			ret += lp;
		} else {
			for (int i=0; i<sub.length-2; i+=2) {
				String next = indent + sub[i+1] + sub[i+2];
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
			for (int i=0; i<sub.length-2; i+=2) {
				String ind = indent + IDisplayStyle.lineIndent;
				String suf = "";
				if (i == last)
					suf += suffix;
				if (i > 0) {
					String next = indent + lp + sub[i+1] + sub[i+2] + suf;
					if (esinl || (strlen(next) > width)) {
						// new line
						ret += lp + "\n" + indent;
						if (cleanup(sub[i+1]).charAt(0) != ' ')
							ret += ' ';
						lp = "";
					}
				}
				String s1 = bl(lp, sub[i+1], sub[i+2] + suf, ind);
				ret += firstLines(s1);
				lp = lastLine(s1);
			}
			ret += lp;
		}
		return ret;
	}
	
	@Override
	public String breakLines(String str, int spos) {
		String start = "";
		for (int i=0; i<spos; i++)
			start += " ";
		String ret = bl(start, str, "", conf.indent);
		ret = ret.substring(spos);
		return ret;
	}

}
