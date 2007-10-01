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

	private static final String[] RANGE_NAMES = {
		"not set yet", "annotation", "instruction", "method", "class"
	};
	
	private BCClass bcc;
	private String code;
	private String prefix;
	private String toRemove = "";
	private String toAdd = "";
	private String suffix;
	private int begin = -1;
	private int end = -1;
	private Parsing parser;
	private int o_begin = -1;
	private int o_end = -1;
	private BCPrintableAttribute attr;
	private SingleList instr;
	private BCMethod method;
	private int range = -1;
	private boolean modified = false;
	private boolean correct = true;
	// modified ==> o_begin <= begin < end <= o_end

	public CodeFragment(BCClass bcc, String code) {
		this.bcc = bcc;
		this.code = code;
	}

	public void addChange(int cfrom, int length, String nc) {
		int cto = cfrom + length;
		if (cfrom > cto)
			throw new RuntimeException(
			"wrong parameter values: cfrom > cto");
		if (cto > code.length())
			throw new RuntimeException("invalid position: "
					+ cto + " (length = " + code.length() + ")");
		if (cfrom < 0)
			throw new RuntimeException("invalid parameter: "
					+ cfrom + " < 0");
		if (!modified) {
			begin = cfrom;
			end = cto;
			toRemove = code.substring(cfrom, cto);
			toAdd = nc;
			modified = true;
		} else {
			if (cto <= begin) {
				//       oooooo
				// nnnn
				MLog.putMsg(MLog.PDebug, "branch no 1");
				toRemove = code.substring(cfrom, begin) + toRemove;
				toAdd = nc + code.substring(cto, begin) + toAdd;
				begin = cfrom;
			} else if ((cfrom <= begin) && (cto > begin) && (cto <= end)) {
				//       oooooo
				//    nnnnnn
				MLog.putMsg(MLog.PDebug, "branch no 2");
				toRemove = code.substring(cfrom, begin) + toRemove;
				toAdd = nc + toAdd.substring(cto - begin);
				begin = cfrom;
			} else if ((cfrom <= begin) && (cto > end)) {
				//       oooooo
				//    nnnnnnnnnnn
				MLog.putMsg(MLog.PDebug, "branch no 3");
				toRemove = code.substring(cfrom, begin)
					+ toRemove + code.substring(end, cto);
				toAdd = nc;
				begin = cfrom;
				end = cto;
			} else if ((cfrom > begin) && (cto <= end)) {
				//       oooooo
				//         nn
				MLog.putMsg(MLog.PDebug, "branch no 4");
				toAdd = toAdd.substring(0, cfrom - begin)
					+ nc + toAdd.substring(cto - begin);
			} else if ((cfrom > begin) && (cfrom <= end) && (cto > end)) {
				//       oooooo
				//         nnnnnnn
				MLog.putMsg(MLog.PDebug, "branch no 5");
				toRemove = toRemove + code.substring(end, cto);
				toAdd = toAdd.substring(0, cfrom - begin) + nc;
				end = cto;
			} else if (cfrom > end) {
				//       oooooo
				//               nnnn
				MLog.putMsg(MLog.PDebug, "branch no 6");
				toRemove = toRemove + code.substring(end, cto);
				toAdd = toAdd + code.substring(end, cfrom) + nc;
				end = cto;
			}
		}
		prefix = code.substring(0, begin);
		suffix = code.substring(end);
		end += toAdd.length() - (end - begin);
		code = prefix + toAdd + suffix;
	}
	
	public void performChanges() {
		correct = false;
		//TODO: compute changes range (set o_begin, o_end and range)
		MLog.putMsg(MLog.PInfo, toString()); //rm
		//TODO: check wether code is correct and parse it
		if (range == RANGE_ANNOT) {
			//TODO
		} else if (range == RANGE_INSTRUCTION) {
			//TODO
		} else if (range == RANGE_METHOD) {
			//TODO
		} else if (range == RANGE_CLASS) {
			//TODO
		} //else throw new RuntimeException("invalid range: " + range);
		modified = false;
		begin = o_begin = o_end = end = range = -1;
	}

	public void modify(int cfrom, int length, String nc) {
		addChange(cfrom, length, nc);
		performChanges();
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
		int[] loc = {-1, -1, -1, -1}; // method, instruction, minor, in_comment
		//TODO: compute changes range (cfrom, cto)
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
						//FIXME! do not trust pc numbers, use position in instructionList instead!
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
		if (!modified)
			return "code hasn't been modified yet";
		String p = prefix;
		String s = suffix;
		if (begin > 100)
			p = "... " + prefix.substring(((begin - 10) / 100) * 100);
		if (suffix.length() > 100)
			s = suffix.substring(0, (end + 10) % 100) + " ...";
		String ret = "*** removed code: ***\n";
		ret += toRemove;
		ret += "\n*** new (modified) code: ***\n";
		ret += p + "##" + toAdd + "##" + s;
		ret += "\n*** CodeFragment status: ***";
		ret += "\ntotal length: " + code.length();
		ret += "\nchanged fragment: " + begin + " to " + end;
		if (o_begin >= 0)
			ret += "\naffected fragment: " + o_begin + " to " + o_end;
		ret += "\nchanges level: " + RANGE_NAMES[range+1];
		ret += "\ncode is currently " + (correct ? "correct" : "incorrect");
		return ret;
	}
	
	public String getCode() {
		return code;
	}

	public boolean isCorrect() {
		return correct;
	}
}
