package annot.textio;

import org.antlr.runtime.RecognitionException;

import test.OldTests;

import annot.attributes.BCPrintableAttribute;
import annot.attributes.SingleList;
import annot.bcclass.BCClass;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;

public class CodeFragment {

	private static final boolean goQuickParse = false;
	private static final boolean goShowDecoratedCode = true;
	
	private BCClass bcc;
	private String oldCode;
	private String code;
	private String prefix;
	private String toAdd;
	private String toRemove;
	private String suffix;
	private String errMsg = "";
	private int begin;
	private int end;
	private int oldEnd;
	private boolean modified = false;
	private boolean correct = true;
	private String last_parsed = ""; //rm
	private int cp_hash = 0; //rm
	
	public CodeFragment(BCClass bcc, String code) {
		this.bcc = bcc;
		this.code = code;
		this.oldCode = code;
	}

	private void showMsg(String msg) {
		MLog.putMsg(MLog.PInfo, msg);
		errMsg = msg;
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
		oldEnd = end;// cp_hash = toRemove.length() - toAdd.length();//rm
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

	public static boolean isAttributeStr(String str) {
		String[] all = getAllAttributeNames();
		for (int i = 0; i < all.length; i++)
			if (all[i].equals(str))
				return true;
		return false;
	}

	public static boolean isNumber(String str) {
		return str.matches("^\\-?[0-9]+");
	}

	public static String getKeyword(String line) {
		//XXX shouln't it return an Object containing
		//	type, number or annotation's keyword?
		if (line.length() < 3)
			return "";
		if (("EOM".equals(line))
			|| ("EOD".equals(line))
			|| ("EOA".equals(line)))
				return line;
		if (line.matches("^.* class .*$")) //?
			return "class";
		if (line.matches("^package .*$"))
			return "package";
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
			if (line.indexOf(anames[i]) >= 0)
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

	public boolean isKeyword(String line) {
		return isAttributeStr(getKeyword(line));
	}
	
	private boolean isNewAnnotLine(String line) {
		if (isKeyword(line))
			return true;
		if (line.matches(Parsing.escape(IDisplayStyle.comment_start)))
			return true;
		if (line.matches(Parsing.escape(IDisplayStyle.comment_end)))
			return true;
		return false;
	}
	
	@Deprecated
	private boolean quickParse() {
		//XXX low quality (may contain errors)
		if (!goQuickParse)
			return false;
		//DONE check if changes affected only single annotation
		int lstart = getLineOfOffset(code, begin);
		int loldEnd = getLineOfOffset(oldCode, oldEnd);
		int lnewEnd = getLineOfOffset(code, end);
		if (isKeyword(code.split("\n")[lstart]))
			if (!isKeyword((prefix+"\n").split("\n")[lstart])) {
				showMsg("annotation's keyword affected");
				return false;
			}
		if (isKeyword(oldCode.split("\n")[lstart]))
			if (!isKeyword((prefix+"\n").split("\n")[lstart])) {
				showMsg("annotation's keyword affected");
				return false;
			}
		if (oldCode.split("\n")[loldEnd].endsWith(IDisplayStyle.comment_end))
			if (!(oldCode+"\n").split("\n")[0].endsWith(IDisplayStyle.comment_end)) {
				showMsg("end of coment affected");
				return false;
			}
		if (isKeyword(oldCode.split("\n")[loldEnd]))
			if (!isKeyword((oldCode+"\n").split("\n")[loldEnd])) {
				showMsg("other annotation's keyword affected");
				return false;
			}
		if (code.split("\n")[lnewEnd].endsWith(IDisplayStyle.comment_end))
			if (!(code+"\n").split("\n")[0].endsWith(IDisplayStyle.comment_end)) {
				showMsg("end of coment affected");
				return false;
			}
		if (isKeyword(code.split("\n")[lnewEnd]))
			if (!isKeyword((code+"\n").split("\n")[lnewEnd])) {
				showMsg("other annotation's keyword affected");
				return false;
			}
		String[] rlines = toRemove.split("\n");
		for (int i=0; i<rlines.length; i++)
			if (isNewAnnotLine(rlines[i])) {
				showMsg("added or removed fragment contains annotation borders");
				return false;
			}
		//DONE parse modified annotations
		String[] lines = code.split("\n");
		int pos = lnewEnd + 1;
		for (;; pos++) {
			if (isNewAnnotLine(lines[pos]))
				break;
			if (pos >= lines.length) {
				showMsg("cannot find end of comment");
				return false;
			}
		}
		String toParse = "";
		if (!isKeyword(lines[pos]))
			toParse = lines[pos];
		pos--;
		for (;; pos--) {
			toParse = lines[pos] + "\n" + toParse;
			if (isNewAnnotLine(lines[pos]))
				break;
			if (pos <= 0) {
				showMsg("cannot find beginning of comment");
				return false;
			}
		}
		int anr = -1;
		for (; pos >= 0; pos--)
			if (isKeyword(lines[pos]))
				anr++;
		toParse = Parsing.purge(toParse);
		MLog.putMsg(MLog.PInfo, "code to be parsed:\n" + toParse);
		MLog.putMsg(MLog.PInfo, "parsing annotation's number: " + anr);
		BCPrintableAttribute pa = bcc.getAllAttributes()[anr];
		try {
			pa.parse(toParse);
		} catch (RecognitionException e) {
			showMsg("syntax error");
			correct = false;
			return true;
		}
		MLog.putMsg(MLog.PNotice, "quickChange parsed annotation successfully.");
		return true;
	}
	
	public static String decorate(String code) {
		String[] lines = code.split("\n");
		boolean met = true;
		boolean decl = false;
		int last_eoc = -1;
		int last_boc = -1;
		for (int l=lines.length - 1; l >= 0; l--) {
			String line = lines[l];
			String kw = getKeyword(line);
			boolean annot = false;
			if (isAttributeStr(kw)) {
				lines[l] = "EOA\n" + lines[l];
				annot = true;
			}
			if (lines[l].endsWith(IDisplayStyle.comment_end)) {
				lines[l] = lines[l] + "\nEOA";
				annot = true;
			}
			if (met) {
				if (isNumber(kw)) {
					lines[l] += "\nEOM";
					met = false;
				} else if (!decl) {
					if (line.endsWith(IDisplayStyle.comment_end))
						last_eoc = l;
					if (IDisplayStyle._requires.equals(kw)) {
						last_eoc = last_boc = -1;
					} else if (isAttributeStr(kw)) {
						if (last_eoc == -1) {
							MLog.putMsg(MLog.PNotice, "attribute keyword outside comment");
							return null;
						}
						lines[last_eoc] += "\nEOD";
						decl = true;
					}
					if (line.startsWith(IDisplayStyle.comment_start))
						last_boc = l - 1;
				}
			}
			if ("method".equals(kw)) {
				last_boc = l;
				met = true;
			}
		}
		if (last_eoc < 0)
			last_eoc = last_boc;
		if (!decl && (last_eoc >= 0))
			lines[last_eoc] += "\nEOD";
		String newCode = "";
		for (int l=0; l<lines.length; l++)
			newCode += lines[l] + "\n";
		MLog.putMsg(MLog.PDebug, OldTests.xxx);
		MLog.putMsg(MLog.PDebug, "newCode:\n" + newCode);
		return newCode;
	}
	
	public static int newPos(String oldCode, String newCode, int oldPos) {
		String oldLines[] = oldCode.split("\n");
		String newLines[] = newCode.split("\n");
		int diff = 0;
		int j=0;
		int lnr = getLineOfOffset(oldCode, oldPos);
		for (int i=0; i<=lnr; i++) {
			for (int x=0; x<2; x++)
				if (!oldLines[i].equals(newLines[j])) {
					diff += newLines[j].length() + 1;
					j++;
				}
			if (!oldLines[i].equals(newLines[j]))
				throw new RuntimeException("error in newPos()!");
			j++;
		}
		return oldPos + diff;
	}
	
	public static CodePosition where(String code, int pos) {
		int lnr = getLineOfOffset(code, pos);
		return where(code, lnr, pos - getLineOffset(code, lnr));
	}

	public static CodePosition where(String code, int lnr, int lpos) {
		if (code.indexOf("\n") < 0) {
			MLog.putMsg(MLog.PInfo, "code too short");
			return null;
		}
		CodePosition cpos = new CodePosition(code);
		//DONE add end of declarations and end of method marks
		String newCode = decorate(code);
		if (newCode == null)
			throw new RuntimeException("error in where()");
		int pos = getLineOffset(code, lnr) + lpos;
		int pos1 = newPos(code, newCode, pos);
		lnr = getLineOfOffset(newCode, pos1);
		lpos = pos1 - getLineOffset(newCode, lnr);
		//DONE check comments parenthness (/* */) and keywords
		if (newCode.indexOf("\nEOD\n") < 0) {
			MLog.putMsg(MLog.PInfo, "no EOD found");
			return null;
		}
		String[] lines = newCode.split("\n");
		boolean inComment = false;
		for (int l=0; l<lines.length; l++) {
			String line = lines[l];
			if (line.startsWith(IDisplayStyle.comment_start)) {
				if (inComment) {
					MLog.putMsg(MLog.PInfo, "invalid comment parenthness: /*/*");
					return null;
				}
				inComment = true;
			}
			String kw = getKeyword(line);
			if (inComment) {
				if (("mthod".equals(kw))
					|| ("class".equals(kw))
					|| ("package".equals(kw))
					|| (isNumber(kw))) {
						MLog.putMsg(MLog.PInfo, "invalid keyword in comment: " + kw);
						return null;
					}
			} else {
				if (isAttributeStr(kw)) {
					MLog.putMsg(MLog.PInfo, "invalid keyword outside comment");
					return null;
				}
			}
			if (line.endsWith(IDisplayStyle.comment_end)) {
				if (!inComment) {
					MLog.putMsg(MLog.PInfo, "invalid comment parenthness: */*/");
					return null;
				}
				inComment = false;
			}
		}
		//DONE compute positions of affected code
		int anr = -1;
		boolean nexta = false;
		int inr = 0;
		int mnr = 0;
		int pc = -2;
		String keyword = null;
		boolean inCA = true;
		int inMspec = 0;
		for (int l=lnr; l>=0; l--) {
			String line = lines[l];
			String kw = getKeyword(line);
			if ((keyword == null) && (isAttributeStr(kw)))
				keyword = kw;
			if ("EOA".equals(kw) && (!nexta))
				anr++;
			if (inMspec == 0) {
				if ("EOM".equals(kw) || ("EOD".equals(kw)))
					inMspec = 1;
				if ("method".equals(kw))
					inMspec = -1;
			}
			if (isNumber(kw) || "EOM".equals(kw)
				|| "EOD".equals(kw) || "method".equals(kw))
					nexta = true;
			if (isNumber(kw) && (mnr == 0) && (l < lnr))
				inr++;
			if ("EOM".equals(kw))
				mnr++;
			if ("EOD".equals(kw))
				inCA = false;
		}
		int mcnt = mnr;
		int acnt = anr;
		int icnt = inr;
		boolean nextInstr = false;
		boolean nextMet = false;
		for (int l=lnr; l<lines.length; l++) {
			String line = lines[l];
			String kw = getKeyword(line);
			if (isNumber(kw) && (pc == -2)) {
				pc = Integer.parseInt(kw);
				nextInstr = true;
			}
			if ("EOD".equals(kw))
				nextInstr = true;
			if (isNumber(kw) && (!nextMet))
				icnt++;
			if ("EOM".equals(kw)) {
				mcnt++;
				nextMet = true;
				nextInstr = true;
			}
			if ("EOA".equals(kw) && !nextInstr)
				acnt++;
		}
		if (inCA) {
			mnr = inr = pc = -1;
			inMspec = -1;
		}
		if (inMspec == 1) {
			cpos.setInMethodSpec(true);
			inr = pc = anr = -1;
		}
		cpos.setPc(pc);
		cpos.setInClassAttribute(inCA);
		cpos.setKeyword(keyword);
		cpos.setMet_cnt(mcnt);
		if (anr >= 0)
			cpos.setAnnot_cnt(acnt);
		if (inr >= 0)
			cpos.setInstr_cnt(icnt);
		cpos.setMet_nr(mnr);
		cpos.setInstr_nr(inr);
		cpos.setAnnot_nr(anr);
		return cpos;
	}
	
	public void performChanges() {
		correct = true;
		errMsg = "";
		if (quickParse())
			return;
		if (goShowDecoratedCode)
			MLog.putMsg(MLog.PInfo, decorate(code));
		//DONE compute positions of affected code
		CodePosition cp_start = where(code, begin);
		CodePosition cp_old = where(oldCode, oldEnd);
		CodePosition cp_new = where(code, end);
		cp_hash = 0;
		if (cp_start != null)
			cp_hash += cp_start.hash();
		if (cp_old != null)
			cp_hash += cp_old.hash();
		if (cp_new != null)
			cp_hash += cp_new.hash();
		MLog.putMsg(MLog.PInfo, "changes positions:");
		MLog.putMsg(MLog.PInfo, "begin  : " + cp_start);
		MLog.putMsg(MLog.PInfo, "old end: " + cp_old);
		MLog.putMsg(MLog.PInfo, "new end: " + cp_new);
		if ((cp_start == null) || (cp_old == null) || (cp_new == null)) {
			showMsg("couldn't find codePositions due to syntax errors");
			correct = false;
			return;
		}
		//FIXME! change unaffected fragments to stubs
		boolean decl = true;
		boolean mspec = true;
		boolean affd = cp_start.isInClassAttribute();
		int mnr = 0;
		boolean affm = true;
		int inr = 0;
		boolean affi = true;
		int anr = -1;
		boolean affa = true;
		boolean mma = (cp_start.getMet_nr() != cp_old.getMet_nr())
			|| (cp_start.getMet_nr() != cp_new.getMet_nr())
			|| (cp_start.getMet_cnt() != cp_old.getMet_cnt())
			|| (cp_start.isInClassAttribute() != cp_old.isInClassAttribute())
			|| (cp_start.isInClassAttribute() != cp_new.isInClassAttribute());
		boolean mia = mma || (cp_start.getInstr_nr() != cp_old.getInstr_nr())
			|| (cp_start.getInstr_nr() != cp_new.getInstr_nr())
			|| (cp_start.getInstr_cnt() != cp_old.getInstr_cnt());
		String newCode = decorate(code);
		String[] lines = newCode.split("\n");
		for (int l=0; l<lines.length; l++) {
			String line = lines[l];
			// empty lines, headers
			if ("".equals(line)) {
				lines[l] = null;
				continue;
			}
			String kw = getKeyword(line);
			if (("class".equals(kw)) || ("package".equals(kw))) {
				lines[l] = "[" + kw + "]";
				continue;
			}
			// class attributes
			if ("EOD".equals(kw)) {
				if (!affd)
					lines[l] = "\\class attributes unaffected";
				decl = false;
				continue;
			}
			if (decl) {
				if (!affd)
					lines[l] = null;
				continue;
			}
			// methods
			affm = (cp_start.getMet_nr() <= mnr)
			&& ((cp_old.getMet_nr() >= mnr)
				|| (cp_new.getMet_nr() >= mnr)
				|| (cp_old.getMet_cnt()
					!= cp_new.getMet_cnt()));
			if ("EOM".equals(kw)) {
				if (!affm)
					lines[l] = "\\method unaffected";
				mnr++;
				affm = (cp_start.getMet_nr() <= mnr)
				&& ((cp_old.getMet_nr() >= mnr)
					|| (cp_new.getMet_nr() >= mnr)
					|| (cp_old.getMet_cnt()
						!= cp_new.getMet_cnt()));
				inr = 0;
				anr = -1;
				mspec = true;
				continue;
			}
			if (!affm) {
				lines[l] = null;
				continue;
			}
			if ("method".equals(kw)) {
				lines[l] = "[method header]";
				mspec = false;
				continue;
			}
			// instructions
			affi = mma || (cp_start.getInstr_nr() <= inr)
				&& ((cp_old.getInstr_nr() >= inr)
					|| (cp_new.getInstr_nr() >= inr)
					|| (cp_old.getInstr_cnt()
						!= cp_new.getInstr_cnt()));
			if (isNumber(kw)) {
				lines[l] = "[instruction]";
				if (!affi)
					lines[l] = "\\instruction unaffected";
				inr++;
				anr = -1;
				affi = (cp_start.getInstr_nr() <= inr)
				&& ((cp_old.getInstr_nr() >= inr)
					|| (cp_new.getInstr_nr() >= inr)
					|| (cp_old.getInstr_cnt()
						!= cp_new.getInstr_cnt()));
				continue;
			}
			if (!affi && (!mspec)) {
				lines[l] = null;
				continue;
			}
			// annotations
			affa = mia || (cp_start.getAnnot_nr() <= anr)
				&& ((cp_old.getAnnot_nr() >= anr)
					|| (cp_new.getAnnot_nr() >= anr)
					|| (cp_old.getAnnot_cnt()
						!= cp_new.getAnnot_cnt()));
			if (mspec)
				affa = (cp_start.isInMethodSpec())
					|| (cp_old.isInMethodSpec())
					|| (cp_new.isInMethodSpec());
			if ("EOA".equals(kw)) {
				if ((anr == -1) && (mspec))
					lines[l] = null;
				if ((anr >= 0) && (!affa)) {
					if (mspec) {
						lines[l] = "\\method specification unaffected";
					} else {
						lines[l] = "\\annotation unaffected";
					}
				}
				anr++;				
				affa = (cp_start.getAnnot_nr() <= anr)
				&& ((cp_old.getAnnot_nr() >= anr)
					|| (cp_new.getAnnot_nr() >= anr)
					|| (cp_old.getAnnot_cnt()
						!= cp_new.getAnnot_cnt()));
				continue;
			}
			if (!affa) {
				lines[l] = null;
				continue;
			}
		}
		String shortCode = "";
		for (int l=0; l<lines.length; l++)
			if (lines[l] != null)
				shortCode += lines[l] + "\n";
		shortCode = shortCode.replaceAll("\n"
				+ Parsing.escape(IDisplayStyle.comment_start), "\n");
		shortCode = shortCode.replaceAll("\n"
				+ Parsing.escape(IDisplayStyle.comment_next), "\n");
		shortCode = shortCode.replaceAll(
				Parsing.escape(IDisplayStyle.comment_end)
				+ "\n", "\n");
		if (shortCode.startsWith(IDisplayStyle.comment_start))
			shortCode = shortCode.substring(IDisplayStyle.comment_length);
		while (shortCode.indexOf("\n\n") >= 0)
			shortCode = shortCode.replaceAll("\n\n", "\n");
		last_parsed = shortCode;
		MLog.putMsg(MLog.PInfo, "code to be parsed:\n" + shortCode);
		//TODO create grammar for parsing bytecode
		//TODO check correctness of new code fragment
		//TODO and parse it into bcc.
	}
	
	public void resetChanges() {
		oldCode = code;
		begin = end = oldEnd = -1;
		toAdd = toRemove = prefix = suffix = null;
		modified = false;
	}
	
	public void modify(int cfrom, int length, String nc) {
		addChange(cfrom, length, nc);
		performChanges();
		MLog.putMsg(MLog.PInfo, toString());
		resetChanges();
	}
	
	public int hash() {
		int h = CodePosition.StrHash(code);
		h += CodePosition.StrHash(oldCode);
		h += CodePosition.StrHash(prefix);
		h += CodePosition.StrHash(toRemove);
		h += CodePosition.StrHash(toAdd);
		h += CodePosition.StrHash(suffix);
		h += CodePosition.StrHash(errMsg);
		h += CodePosition.StrHash(last_parsed);
		h += begin + end + oldEnd;
		if (modified) h += 3;
		if (correct) h += 5;
		h += cp_hash;
		return h % 1000;
	}

	public String toString() {
		if (!modified)
			return "code hasn't been modified yet";
		String ret = "******** removed code: *********\n";
		ret += toRemove;
		ret += "\n*** current (modified) code: ***\n";
		ret += prefix + "##" + toAdd + "##" + suffix;
		ret += "\n*** CodeFragment status: ***";
		ret += "\ntotal length: " + code.length();
		ret += "\nchanged fragment: " + begin + " to " + end;
		ret += "\ncode is currently " + (correct ? "correct" : "incorrect");
		if (errMsg.length() > 0)
			ret += "\nlast error message: " + errMsg;
		ret += "\nhash: " + hash();
		return ret;
	}

	public String getCode() {
		return code;
	}

	public boolean isCorrect() {
		return correct;
	}

	public String getErrMsg() {
		return errMsg;
	}
}
