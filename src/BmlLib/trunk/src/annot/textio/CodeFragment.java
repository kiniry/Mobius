package annot.textio;

import org.antlr.runtime.RecognitionException;

import annot.attributes.BCPrintableAttribute;
import annot.attributes.InCodeAttribute;
import annot.attributes.SingleList;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;

public class CodeFragment {

	public static final int RANGE_CLASS = 3;
	public static final int RANGE_METHOD = 2;
	public static final int RANGE_INSTRUCTION = 1;
	public static final int RANGE_ANNOT = 0;
	
	private BCClass bcc;
	private String code;
	private int begin;
	private int end;
	private Parsing parser;
	private int o_begin;
	private int o_end;
	private String prefix;
	private String suffix;
	private String oldc;
	private BCPrintableAttribute attr;
	private SingleList instr;
	private BCMethod method;
	private int range = -1;
	private boolean correct = true;
	private String last_correct;

	public CodeFragment(BCClass bcc, String code) {
		this.bcc = bcc;
		this.code = code;
		this.last_correct = code;
	}
	
	public void modify(int cfrom, int cto, String newCode) {
		if (cfrom >= cto)
			throw new RuntimeException(
			"wrong parameter values: cfrom >= cto");
		if (cto > code.length())
			throw new RuntimeException("invalid position: "
					+ cto + " (length = " + code.length() + ")");
		if (cfrom < 0)
			throw new RuntimeException("invalid parameter: "
					+ cfrom + " < 0");
		//TODO
		correct = false;
	}

	public void updatePCNumbers() {
		//TODO
	}
	
	public static String getKeyword(String line) {
		if (line.length() < 3)
			return "";
		if ((line.indexOf(":") < 0)
			&& (line.indexOf("*") < 0)
			&& (line.charAt(0) != ' ')
			&& (line.matches("^.+\\(.*\\)$"))
			) return "method";
		if (line.matches("^[0-9]+: .*$"))
			return ""+Integer.parseInt(
				line.substring(0, line.indexOf(":")));
		String[] anames = CodeSearch.getAllAttributeNames();
		for (int i=0; i<anames.length; i++)
			if (line.indexOf(anames[i]) > 0)
				return anames[i];
		if (line.startsWith(IDisplayStyle.comment_start)) {
			if (line.endsWith(IDisplayStyle.comment_end))
				return "single_line_comment";
			return "comment_start";
		}
		if (line.endsWith(IDisplayStyle.comment_end))
			return "comment_end";
		return "";
	}
	
	public static int[] where(String code, int pos) {
		int lnr = getLineOfOffset(code, pos);
		return where(code, lnr, pos - getLineOffset(code, lnr));
	}
	
	public static int[] where(String code, int lnr, int lpos) {
		int[] loc = {-1, -1, -1, -1};
		String[] lines = code.split("\n");
		if (lpos > lines[lnr].length() - 1)
			lpos = lines[lnr].length() - 1;
		boolean after_mspec = false;
		boolean inComment = false;
		for (int i=0; i<lines.length; i++) {
			String line = lines[i];
			if (line.startsWith(IDisplayStyle.comment_start))
				inComment = true;
			if (i == lnr)
				loc[3] = inComment ? 1 : 0;
			String kw = getKeyword(line);
			if (inComment) {
				if (i <= lnr) {
					if (kw == IDisplayStyle._requires) {
						loc[0]++;
						after_mspec = true;
					}
					if (CodeSearch.isAttributeStr(kw))
						loc[2]++;
				}
			} else {
				if (i <= lnr)
					loc[2] = -1;
				if (kw == "method") {
					if ((i <= lnr) && (!after_mspec))
						loc[0]++;
					after_mspec = false;
					if ((i >= lnr) && (loc[1] == -1))
						loc[1] = -2;
				} else if (CodeSearch.isNumber(kw)) {
					if ((i >= lnr) && (loc[1] == -1))
						loc[1] = Integer.parseInt(kw);
				}
			}
			if (i == lnr) {
				if (line.startsWith(IDisplayStyle.comment_start))
					if (lpos < IDisplayStyle.comment_length)
						loc[2] = -1;
				if (line.endsWith(IDisplayStyle.comment_end))
					if (lpos >= line.length() - IDisplayStyle.comment_length)
						loc[2] = -1;
			}
			if (line.endsWith(IDisplayStyle.comment_end))
				inComment = false;
		}
		return loc;
	}

	public static int getLineOfOffset(String code, int pos) {
		if (code.charAt(pos) == '\n')
			return code.substring(0, pos).split("\n").length;
		return code.substring(0, pos+1).split("\n").length-1;//?
	}
	
	public static int getLineOffset(String code, int lnr) {
		String[] lines = code.split("\n");
		int pos = 0;
		for (int i=0; i<lnr; i++)
			pos += lines[i].length() + 1;
		return pos;
	}

	public String toString() {
		return "?";
	}
	
	public String getCode() {
		return code;
	}

	public void refresh() {
		//TODO;
	}
	
	public int getRange() {
		return range;
	}
	
	public boolean correct() {
		return correct;
	}
}
