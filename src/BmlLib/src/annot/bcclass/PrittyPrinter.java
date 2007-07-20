package annot.bcclass;

import java.util.Vector;

public class PrittyPrinter implements IPrittyPrinter {

	private BMLConfig conf;
	
	public PrittyPrinter(BMLConfig conf) {
		this.conf = conf;
	}

	/**
	 * Adds vartical line after screen width (conf.max_total_line_width) column.
	 * 
	 * @param s - string (single line, without \n) to be processed
	 * @return s with "|" inserted after screen width's column
	 */
	private String filter2(String s) {
		String result = "";
		s = s.replaceAll("\t", "        ");
		if (s.length() < conf.max_total_line_width) {
			result = s;
			for (int i=s.length(); i<conf.max_total_line_width; i++)
				result += " ";
			result += "|";
		} else {
			result = s.substring(0, conf.max_total_line_width) + "|" + s.substring(conf.max_total_line_width);
		}
		return result;
	}
	
	/**
	 * Removes trailing spaces from given line.
	 * 
	 * @param s - string (single line, without \n) to be processed
	 * @return s with trailing spaces removed.
	 */
	private String filter1(String s) {
		int i = s.length() - 1;
		while ((i>0) && (s.charAt(i) == ' '))
			i--;
		if (i<=0)
			return "";
		return s.substring(0, i+1);
	}
	
	/**
	 * Applies some filters for each line of generated code, to improve it's look.
	 * Should be called after generating code.
	 */
	public String afterDisplay(String str) {
		String result = "";
		String[] lines = str.split("\n");
		for (int i=0; i<lines.length; i++)
			result += filter2(filter1(lines[i])) + "\n";
		return result;
	}
	
	/**
	 * splits given expression into subexpressions.
	 * 
	 * @param str - string representation of expression, with infix blocks marked using constants in BMLConfig,
	 * 				and without line breaks.
	 * @return String array of infix operators on even positions, and following subexpressions
	 * 				on odd positions. Last element is an empty string, to avoid ArrayIndexOutOfBounds errors.
	 */
	private String[] splitRoot(String str) {
		Vector<String> v = new Vector<String>();
		int level = 0;
		String sub = "";
		for (int p=0; p<str.length(); p++) {
			char ch = str.charAt(p);
			if (ch == conf.expr_block_start) {
				if (level == 0) {
					v.add(sub);
					sub = "";
				} else {
					sub += conf.expr_block_start;
				}
				level++;
			} else if (ch == conf.expr_block_end) {
				level--;
				if (level < 0)
					throw new RuntimeException(str.substring(0, p)+"#"+str.substring(p));
				if (level == 0) {
					v.add(sub);
					sub = "";
				} else {
					sub += conf.expr_block_end;
				}
			} else {
				sub += ch;
			}
		}
		if ((v.size() == 0) && (str.lastIndexOf(conf.expr_block_start) >= 0))
			return (splitRoot(str.substring(1, str.length()-1)));
		v.add(sub);
		v.add("");
		String[] result = new String[v.size()];
		for (int i=0; i<v.size(); i++)
			result[i] = v.elementAt(i);
		return result;
	}
	
	/**
	 * Removes blocks marks from given string.
	 * 
	 * @param str - a String with BMLConfig.expr_block_start and BMLConfig.expr_block_end characters.
	 * @return str without characters mentioned above.
	 */
	private String cleanup(String str) {
		String result = "";
		for (int i=0; i<str.length(); i++) {
			char ch = str.charAt(i);
			if ((ch != conf.expr_block_start) && (ch != conf.expr_block_end))
				result += ch;
		}
		return result;
	}
	
	/**
	 * Computes length of a string, without block marks.
	 * 
	 * @param str - a String with blocks marked as in procedures above.
	 * @return length of str without block marks.
	 */
	private int strlen(String str) {
		return cleanup(str).length();
	}

	/**
	 * Insert line-breaks and indentions to given String.
	 * 
	 * @param str - String representation of an expression with blocks marked with BMLConfig.expr_block_start
	 * 				and BMLConfig.expr_block_end and without newLines ("\n")
	 * @param start - used characters in current line, excluding standard indention
	 * @param end -	used characters at the end of last generated lines
	 * @param w -	indention to be used at the root of expression <code>str</code>.
	 * @return <code>str</code> with line-breaks and indentoin when nessessery. No line of this expression
	 * 				should be longer than max_total_line_width defined in BMLConfig (if possible).
	 * 				The first line should be shorter by at least <code>start</code> lines, and the last
	 * 				line by <code>end</code> lines.
	 */
	private String breakLines(String str, int start, int end, String w) {
		String result = "";
		if (conf.start_line_pos() + strlen(str) < conf.max_total_line_width - start - end)
			return cleanup(str);
		String[] sub = splitRoot(str);
		if (sub.length == 1)
			return cleanup(sub[0]);
		String oldInd = conf.indent;
		conf.indent = w;
		result += sub[0];
		start += strlen(sub[0]);
		boolean ok = true;
		for (int i=1; i<sub.length-1; i+=2) {
			int epos = (i > sub.length - 4) ? end : 0;
			String s = sub[i] + sub[i+1];
			if ((conf.start_line_pos() + start + strlen(s) <= conf.max_total_line_width - epos) && ok) {
				result += cleanup(s);
				start += strlen(s);
			} else {
				String[] sub2 = splitRoot(sub[i]);
				boolean b = false;
				if (sub2.length > 3)
					b = breakLines(sub2[1], 0, sub2[2].length()+epos, w).lastIndexOf("\n") >= 0; //XXX ??
				String e = breakLines(sub[i], 0, sub[i+1].length()+epos, b ? w : w+conf.lineIndent);
				if (e.charAt(0) != '\n') {
					result += conf.newLine();
					start = 0;
					if (e.substring(1).lastIndexOf("\n") >= 0)
						ok = false;
				}
				result += e + sub[i+1];
				start += result.length() - (result.lastIndexOf("\n") + 1) - conf.start_line_pos();
			}
		}
		conf.indent = oldInd;
		return result;
	}
	
	/**
	 * Adds line-breaking with indention to str (first line should be shorter by <code>spos</code> characters).
	 */
	public String breakLines(String str, int spos) {
		return breakLines(str, spos, 0, conf.indent);
	}
}
