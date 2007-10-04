package annot.textio;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.attributes.BCPrintableAttribute;
import annot.attributes.InCodeAttribute;
import annot.attributes.SingleList;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;

public class CodeFragment {

	public static final int RANGE_CLASS = 4;
	public static final int RANGE_CLASS_ATTR = 3;
	public static final int RANGE_METHOD = 2;
	public static final int RANGE_INSTRUCTION = 1;
	public static final int RANGE_ANNOT = 0;
	private static final int CONTEXT_LENGTH = 200;

	public static final String[] RANGE_NAMES = {
		"not set yet",
		"annotation",
		"instruction",
		"method",
		"class attribute",
		"class"
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
	private InstructionHandle instr;
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
		computeRange();//mv
	}

	private int getCommonRange(CodePosition b, CodePosition e) {
		if ((b.isInClassAttribute()) && (e.isInClassAttribute()))
			return RANGE_CLASS_ATTR;
		int r = RANGE_ANNOT;
		if (b.getMin_nr() != e.getMin_nr())
			r = RANGE_INSTRUCTION;
		if (!(b.isInComment() && e.isInComment()))
			r = RANGE_METHOD;
		if (b.getInstr_nr() != e.getInstr_nr())
			r = RANGE_METHOD;
		if (b.getMet_nr() != e.getMet_nr())
			r = RANGE_CLASS;
		return r;
	}
	
	private void computeRange() {
		String oldCode = prefix + toRemove + suffix;
		int diff = toRemove.length() - toAdd.length();
		MLog.putMsg(MLog.PDebug2, "diff="+diff+"\nold code:\n"+oldCode);
		CodePosition oldStart = where(oldCode ,begin);
		CodePosition oldEnd = where(oldCode, end + diff);
		CodePosition newStart = where(code, begin);
		CodePosition newEnd = where(code, end);
		int r1 = getCommonRange(oldStart, oldEnd);
		int r2 = getCommonRange(newStart, newEnd);
		range = (r1 > r2) ? r1 : r2;
		method = null;
		instr = null;
		attr = null;
		//TODO what to do with class invariant?
		if (range <= RANGE_CLASS_ATTR) {
			int min = oldStart.getMin_nr();
			if ((oldEnd.getMin_nr() == min)
					&& (newStart.getMin_nr() == min)
					&& (newEnd.getMin_nr() == min)) {
				if (IDisplayStyle._classInvariant
						.equals(newStart.getKeyword()))
					attr = bcc.getInvariant();
			}
		}
		if (range <= RANGE_METHOD)
			method = bcc.getMethod(newStart.getMet_nr());
		if (range <= RANGE_INSTRUCTION)
			if (newStart.getInstr_nr() == -2) {
				attr = method.getMspec();
				if (attr == null)
					throw new RuntimeException("no method spec.");
			} else if (newStart.getInstr_nr() >= 0) {
				instr = method.getInstructions()
				.getInstructionHandles()
				[newStart.getInstr_nr()];
			}
		if ((range <= RANGE_ANNOT) && (instr != null)) {
			attr = method.getAmap().getAllAt(instr)
			.nth(newStart.getMin_nr());
			if (attr == null)
				throw new RuntimeException("invalid positions in SingleList.");
		}
		o_begin = 0;
		o_end = code.length();
//		pos1 = where(code, begin);
//		pos2 = where(code, end);
		int line_start = getLineOfOffset(code, begin);
		int line_end = getLineOfOffset(code, end);
		int line_count = code.split("\n").length;
		int line_pos1 = begin - getLineOffset(code, line_start);
		int line_pos2 = end - getLineOffset(code, line_end);
		for (int line = line_start; line>=0; line--) {
			CodePosition cpos = where(code, line, line_pos1);
//			int[] pos = where(code, line, line_pos1);
			MLog.putMsg(MLog.PDebug2, cpos.toString());
//			MLog.putMsg(MLog.PDebug2, "line " + line + ": ["+pos[0]+", "+pos[1]+", "+pos[2]+", "+pos[3]+", "+pos[4]+"]");
			if (getCommonRange(cpos, newStart) > range) {
//			if ((pos[0] != pos1[0]) && (range <= RANGE_METHOD)
//				|| (pos[4] != pos1[4]) && (range <= RANGE_INSTRUCTION)
//				|| (pos[2] != pos1[2]) && (range <= RANGE_ANNOT)) {
					o_begin = getLineOffset(code, line+1);
					break;
				}
		}
		MLog.putMsg(MLog.PDebug2, "------");
		for (int line = line_end; line<line_count; line++) {
			CodePosition cpos = where(code, line, line_pos2);
//			int[] pos = where(code, line, line_pos2);
			MLog.putMsg(MLog.PDebug2, cpos.toString());
//			MLog.putMsg(MLog.PDebug2, "line " + line + ": ["+pos[0]+", "+pos[1]+", "+pos[2]+", "+pos[3]+", "+pos[4]+"]");
			if (getCommonRange(cpos, newEnd) > range) {
//			if ((pos[0] != pos1[0]) && (range <= RANGE_METHOD)
//					|| ((pos[4] != pos1[4]) || (pos[3] == 0))
//						&& (range <= RANGE_INSTRUCTION)
//					|| (pos[2] != pos1[2]) && (range <= RANGE_ANNOT)
//					) {
					o_end = getLineOffset(code, line)-1;
					break;
				}
		}
		if ((begin < o_begin) || (end < begin) || (o_end < end)) {
			MLog.putMsg(MLog.PError, "o_begin = " + o_begin);
			MLog.putMsg(MLog.PError, "begin = " + begin);
			MLog.putMsg(MLog.PError, "end = " + end);
			MLog.putMsg(MLog.PError, "o_end = " + o_end);
			throw new RuntimeException("error in computeRange()!");
		}
	}
	
	public void performChanges() {
		correct = false;
		MLog.putMsg(MLog.PInfo, toString()); //rm
		String toParse = code.substring(o_begin, begin)
			+ toAdd + code.substring(end, o_end);
		if (range == -1) {
			MLog.putMsg(MLog.PNotice, "No changes detected!");
		} else if (range == RANGE_ANNOT) {
			toParse = Parsing.purge(toParse);
			MLog.putMsg(MLog.PDebug, "parsing: " + toParse);
			//TODO
		} else if (range == RANGE_INSTRUCTION) {
			//TODO
		} else if (range == RANGE_METHOD) {
			//TODO
		} else if (range == RANGE_CLASS_ATTR) {
			//TODO
		} else if (range == RANGE_CLASS) {
			//TODO
		} else throw new RuntimeException("invalid range: " + range);
	}

	private void applyChanges() {
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
		if (line.startsWith(":"))
			return "-1";
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
	
	public static CodePosition where(String code, int pos) {
		int lnr = getLineOfOffset(code, pos);
		return where(code, lnr, pos - getLineOffset(code, lnr));
	}
	
	public static CodePosition where(String code, int lnr, int lpos) {
//		int[] loc = {-1, -1, -1, -1, -2};
		CodePosition cpos = new CodePosition(code);
		// method, instruction(pc), minor, in_comment,
		// instruction(pos in list).
		//XXX shouldn't it be an object instead of an array?
		String[] lines = code.split("\n");
		if (lpos > lines[lnr].length() - 1)
			lpos = lines[lnr].length() - 1;
		boolean after_mspec = false;
		boolean inComment = false;
		int ipos = 0;
		for (int i=0; i<lines.length; i++) {
			String line = lines[i];
			if (line.startsWith(IDisplayStyle.comment_start))
				inComment = true;
			if (i == lnr)
				cpos.setInComment(inComment);
//				loc[3] = inComment ? 1 : 0;
			String kw = getKeyword(line);
			if (inComment) {
				if (i <= lnr) {
					if (kw == IDisplayStyle._requires) {
						cpos.incMet_nr();
//						loc[0]++;
						after_mspec = true;
					}
					if (CodeSearch.isAttributeStr(kw)) {
						cpos.incMin_nr();
						cpos.setKeyword(kw);
//						loc[2]++;
					}
				}
			} else {
				if (i <= lnr) {
					cpos.setMin_nr(-1);
					cpos.removeKeyword();
//					loc[2] = -1;
				}
				if (kw == "method") {
					if ((i <= lnr) && (!after_mspec))
						cpos.incMet_nr();
//						loc[0]++;
					after_mspec = false;
					if ((i >= lnr) && (cpos.getPc() == -1))
						cpos.setPc(-2);
//					if ((i >= lnr) && (loc[1] == -1))
//						loc[1] = -2;
					ipos = 0;
					if ((i >= lnr) && (cpos.getInstr_nr() == -1))
						cpos.setInstr_nr(-2);
//					if ((i >= lnr) && (loc[4] == -2))
//						loc[4] = -1;
				} else if (CodeSearch.isNumber(kw)) {
					if ((i >= lnr) && (cpos.getPc() == -1))
						cpos.setPc(Integer.parseInt(kw));
//					if ((i >= lnr) && (loc[1] == -1))
//					loc[1] = Integer.parseInt(kw);
					if ((i >= lnr) && (cpos.getInstr_nr() == -1))
						cpos.setInstr_nr(ipos);
//					if ((i >= lnr) && (loc[4] == -2))
//					loc[4] = ipos;
					ipos++;
				}
			}
			if (i == lnr) {
				if (line.startsWith(IDisplayStyle.comment_start))
					if (lpos < IDisplayStyle.comment_length)
						cpos.setMin_nr(-1);
//						loc[2] = -1;
				if (line.endsWith(IDisplayStyle.comment_end))
					if (lpos >= line.length() - IDisplayStyle.comment_length)
						cpos.setMin_nr(-1);
//						loc[2] = -1;
			}
			if (line.endsWith(IDisplayStyle.comment_end))
				inComment = false;
		}
		return cpos;
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
		h += 2*begin + 3*end + 5*o_begin + 7*o_end + 11*range;
		if (attr != null) h += 13;
		if (instr != null) h += 17;
		if (method != null) h += 19;
		if (modified) h += 23;
		if (correct) h += 31;
		return h % 1000;
	}

	public String toString() {
		if (!modified)
			return "code hasn't been modified yet";
		String part1 = code.substring(0, o_begin);
		String part2 = code.substring(o_begin, begin);
		String part3 = code.substring(begin, end);
		String part4 = code.substring(end, o_end);
		String part5 = code.substring(o_end);
		if (!part3.equals(toAdd)) {
			MLog.putMsg(MLog.PError, "part3="+part3+"\ntoAdd="+toAdd);
			throw new RuntimeException("error in CodeFragment!");
		}
		if (o_begin > CONTEXT_LENGTH)
			part1 = "... " + part1.substring(o_begin - CONTEXT_LENGTH);
		if (part5.length() > CONTEXT_LENGTH)
			part5 = part5.substring(0, CONTEXT_LENGTH) + " ...";
		String ret = "*** removed code: ***\n";
		ret += toRemove;
		ret += "\n*** new (modified) code: ***\n";
		ret += part1 + "$$" + part2 + "##" + part3 + "##"
			+ part4 + "$$" + part5;
		ret += "\n*** CodeFragment status: ***";
		ret += "\nknown: class";
		if (method != null)
			ret += ", method";
		if (instr != null)
			ret += ", instruction handle";
		if (attr != null)
			ret += ", annotation";
		ret += "\ntotal length: " + code.length();
		ret += "\nchanged fragment: " + begin + " to " + end;
		if (o_begin >= 0)
			ret += "\naffected fragment: " + o_begin + " to " + o_end;
		ret += "\nchanges level: " + RANGE_NAMES[range+1];
		ret += "\ncode is currently " + (correct ? "correct" : "incorrect");
		ret += "\nhash: " + hash();
		return ret;
	}
	
	public String getCode() {
		return code;
	}

	public int getRange() {
		return range;
	}

	public boolean isCorrect() {
		return correct;
	}
}
