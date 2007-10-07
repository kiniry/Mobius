package annot.textio;

import annot.attributes.BCPrintableAttribute;
import annot.attributes.SingleList;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;

public class CodeFragment {

	private BCClass bcc;
	private String code;
	private String prefix;
	private String toAdd;
	private String toRemove;
	private String suffix;
	private int begin;
	private int end;
	private boolean modified = false;
	private boolean correct = true;
	
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

	public static int getLineOfOffset(String code, int pos) {
		return (code.substring(0, pos)+'.').split("\n").length-1;
	}
	
	public static int getLineOffset(String code, int lnr) {
		String[] lines = code.split("\n");
		int pos = 0;
		for (int i=0; i<lnr; i++)
			pos += lines[i].length() + 1;
		return pos;
	}

	public static String[] getAllAttributeNames() {
		String[] ret = { IDisplayStyle._classInvariant,
				IDisplayStyle._requires, IDisplayStyle._precondition,
				IDisplayStyle._postcondition, IDisplayStyle._assert };
		return ret;
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
		if (line.startsWith(":"))
			return "-1";
		String[] anames = getAllAttributeNames();
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

	public CodePosition where(String code, int pos) {
		int lnr = getLineOfOffset(code, pos);
		return where(lnr, pos - getLineOffset(code, lnr));
	}
	
	private boolean quickChanges() {
		//TODO check if changes affected only single annotation
		//TODO parse modified annotations
		return true;
	}
	
	public CodePosition where(int lnr, int lpos) {
		//TODO add end of declarations and end of method marks
		//TODO check comments parenthness (/* */) and keywords
		//TODO compute positions of affected code
		return null;
	}
	
	public void performChanges() {
		correct = true;
		if (quickChanges())
			return;
		//TODO compute positions of affected code
		//TODO change unaffected fragments to stubs
		//TODO create grammar for parsing bytecode
		//TODO check correctness of new code fragment
		//TODO and parse it into bcc.
	}
	
	public void modify(int cfrom, int length, String nc) {
		addChange(cfrom, length, nc);
		performChanges();
	}
	
	private static int StrHash(String str) {
		int h = 0;
		for (int i=0; i<str.length(); i++)
			h = (h + i * (int)(str.charAt(i))) % 1000000;
		return h;
	}
	
	public int hash() {
		int h = StrHash(code);
		h += StrHash(prefix);
		h += StrHash(toRemove);
		h += StrHash(toAdd);
		h += StrHash(suffix);
		if (modified) h += 23;
		if (correct) h += 31;
		return h % 1000;
	}

	public String toString() {
		if (!modified)
			return "code hasn't been modified yet";
		String ret = "*** removed code: ***\n";
		ret += toRemove;
		ret += "\n*** current (modified) code: ***\n";
		ret += prefix + "##" + toAdd + "##" + suffix;
		ret += "\n*** CodeFragment status: ***";
		ret += "\ntotal length: " + code.length();
		ret += "\nchanged fragment: " + begin + " to " + end;
		ret += "\ncode is currently " + (correct ? "correct" : "incorrect");
		ret += "\nhash: " + hash();
		return ret;
	}

	public String getCode() {
		return code;
	}

	public boolean isCorrect() {
		return correct;
	}
}
