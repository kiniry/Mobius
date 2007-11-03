package annot.textio;

import test.OldTests;

import annot.bcclass.BCClass;
import annot.bcclass.MLog;

/**
 * This class represents BMl of an editing bytecode. It's
 * objects can be contructed  with {@link BCClass} and current
 * String representation of bytecode. You can add one or more
 * changes (using {@link #addChange(int, int, String)}
 * method), then execute these changes using
 * {@link #performChanges()} method (this will parse all
 * that changes merged to one, single change, updating
 * it's {@link BCClass}) and see that it's correct, than call
 * {@link #resetChanges()} method. If some changes has been
 * parsed outside this class, call {@link #resetChanges()}
 * to assume that {@link BCClass} is up to date.
 * It can parse only BML placed somewhere in bytecode,
 * not the bytecode itself. Bytecode changes won't be updated
 * into {@link BCClass}.
 * 
 * @author tomekb
 */
public class CodeFragment {

	/**
	 * Shows code after preprocessing it
	 * by {@link #decorate(String)} method.
	 */
	private static final boolean goShowDecoratedCode = true;
	
	/**
	 * Disable parsing single attributes; for debugging only.
	 */
	private static final boolean goDisableParser = false;
	
	/**
	 * BCClass related with current bytecode.
	 */
	private BCClass bcc;
	
	/**
	 * Old (original) version of bytecode.
	 */
	private String oldCode;
	
	/**
	 * Current bytecode.
	 */
	private String code;
	
	/**
	 * Common prefix for original and current bytecode.
	 */
	private String prefix;
	
	/**
	 * Code that should be added in merged changes
	 * in bytecode.
	 */
	private String toAdd;
	
	/**
	 * Code that should be removed in merged changes
	 * in bytecode.
	 */
	private String toRemove;
	
	/**
	 * Common suffix for original and current bytecode.
	 */
	private String suffix;

	/**
	 * oldCode == prefix + toRemove + suffix;
	 * code == prefix + toAdd + suffix;
	 */
	
	/**
	 * Last error message.
	 */
	private String errMsg = "";
	
	/**
	 * Position of first character on which old and current
	 * bytecodes differs.
	 */
	private int begin;
	
	/**
	 * Position of first unaffected character (in current
	 * bytecode).
	 */
	private int end;

	/**
	 * Position of first unaffected character (in original
	 * bytecode).
	 */
	private int oldEnd;
	
	/**
	 * whether any changes has been added since last
	 * {@link #resetChanges()} call.
	 */
	private boolean modified = false;

	/**
	 * whether current bytecode is correct or not.
	 */
	private boolean correct = true;
	
	// the two fields below are unused, but should be
	// left alone for tests compatibility.
	
	//unused
	private String last_parsed = "";
	
	//unused
	private int cp_hash = 0;
	
	/**
	 * A standard contructor.
	 * 
	 * @param bcc - BCClass related with this bytecode,
	 * @param code - a String representation of bytecode.
	 */
	public CodeFragment(BCClass bcc, String code) {
		this.bcc = bcc;
		this.code = code;
		this.oldCode = code;
	}

	/**
	 * Displays an error message and remembers
	 * it in errMsg field, as last error message.
	 * 
	 * @param msg
	 */
	private void showMsg(String msg) {
		MLog.putMsg(MLog.PInfo, msg);
		errMsg = msg;
	}
	
	/**
	 * Adds a change (effect of bytecode editing) to this
	 * bytecode. A change is replacing one fragment of this
	 * bytecode with another String.
	 * 
	 * @param cfrom - position of first modified character,
	 * @param length - length of removed String,
	 * @param nc - new String added at removed String's
	 * 		position.
	 */
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
		oldEnd = prefix.length() + toRemove.length();
		end = prefix.length() + toAdd.length();
		code = prefix + toAdd + suffix;
	}

	/**
	 * Translates character position in a String to number
	 * of line containing this character.
	 * 
	 * @param code - multi-line String,
	 * @param pos - number of character (offset)
	 * 		in <code>code</code>.
	 * @return Number of line in <code>code</code> containing
	 * 		character with offset <code>pos</code>.
	 */
	private static int getLineOfOffset(String code, int pos) {
		return (code.substring(0, pos)+'.').split("\n").length-1;
	}
	
	/**
	 * Translates line number of a String to character number
	 * (offset).
	 * 
	 * @param code - multi-line String,
	 * @param lnr - number of line in <code>code</code>.
	 * @return Offset of first character of <code>lnr</code>'s
	 * 		line in <code>code</code>.
	 */
	private static int getLineOffset(String code, int lnr) {
		String[] lines = code.split("\n");
		int pos = 0;
		for (int i=0; i<lnr; i++)
			pos += lines[i].length() + 1;
		return pos;
	}

	/**
	 * @return all keywords that can stand at the beginning
	 * 		of an annotation.
	 */
	private static String[] getAllAttributeNames() {
		String[] ret = { IDisplayStyle._classInvariant,
				IDisplayStyle._requires, IDisplayStyle._assert,
				IDisplayStyle._loopspec};
		return ret;
	}

	/**
	 * @return all keywords that can stand at the beginning
	 * 		of an method annotation.
	 */
	private static String[] getMethodAttributeNames() {
		String[] ret = {IDisplayStyle._requires};
		return ret;
	}
	
	/**
	 * Searches for given keyword
	 * in {@link #getAllAttributeNames()}.
	 * 
	 * @param str - a keyword, returned by
	 * 		{@link #getKeyword(String)} method.
	 * @return <b>true</b>, if it is an annotation's keyword,
	 * 		<b>false</b> otherwise.
	 */
	private static boolean isAttributeStr(String str) {
		String[] all = getAllAttributeNames();
		for (int i = 0; i < all.length; i++)
			if (all[i].equals(str))
				return true;
		return false;
	}

	/**
	 * Searches for given keyword
	 * in {@link #getMethodAttributeNames()}
	 * 
	 * @param str - a keyword, returned by
	 * 		{@link #getKeyword(String)} method.
	 * @return <b>true</b>, if it is an method annotation's
	 * 		keyword, <b>false</b> otherwise.
	 */
	private static boolean isMethodAttributeStr(String str) {
		String[] all = getMethodAttributeNames();
		for (int i = 0; i < all.length; i++)
			if (all[i].equals(str))
				return true;
		return false;
	}

	/**
	 * Checks whether given String represents an integer.
	 * 
	 * @param str - a String.
	 * @return whether <code>str</code> is correct String
	 * 		representation of an integer or not.
	 */
	private static boolean isNumber(String str) {
		return str.matches("^\\-?[0-9]+");
	}

	/**
	 * Returns a keyword of given bytecode line.
	 * 
	 * @param line - a line of bytecode.
	 * @return <b>"EOM", "EOD" or "EOA"</b> for the
	 * 			same lines,<br>
	 * 		<b>"package"</b> for package declaration,<br>
	 * 		<b>"class"</b> for class ehader,<br>
	 * 		<b>"method"</b> for method header,<br>
	 * 		<b>pc number</b> for instruction line (<b>-1</b>
	 * 				if it doesn't contain pc number),<br>
	 * 		<b>attribute keyword</b> for first line
	 * 				of an annotation,<br>
	 * 		<b>"comment_start"</b> for beginning of comment,<br>
	 * 		<b>"comment_end"</b> for end of comment,
	 * 		<b>an empty String</b>  otherwise.
	 */
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
		return "";
	}

	private static boolean isCommentStart(String line) {
		return line.matches(" *"+Parsing.escape(IDisplayStyle.comment_start)+"(.|\n)*");
	}

	private static boolean isCommentEnd(String line) {
		return line.matches("(.|\n)*"+Parsing.escape(IDisplayStyle.comment_end)+" *");
	}

	/**
	 * Adds EOD, EOM and EOA marks to given bytecode.
	 * "EOD" line is inserted after class attributes, but
	 * before first method, "EOM" line is inserted after each
	 * method, and "EOA" lines are inserted at the beginning
	 * of each comment and after each annotation.
	 * Use {@link #goShowDecoratedCode} flag to see decorated
	 * code while performing changes (at PInfo display level).
	 * 
	 * @param code - bytecode to be decorated,
	 * @return <code>code</code> with EOD, EOM and EOA marks
	 * 		inserted, or <code>null</code> it <code>code</code>
	 * 		is not correct enough to process it.
	 */
	private static String decorate(String code) {
		String[] lines = code.split("\n");
		boolean met = true;
		boolean decl = false;
		int last_eoc = -1;
		int last_boc = -1;
		int last_eoa = -1;
		for (int l=lines.length - 1; l >= 0; l--) {
			String line = lines[l];
			String kw = getKeyword(line);
			if (isAttributeStr(kw)) {
				lines[l] = "EOA\n" + lines[l];
				last_eoa = l;
			}
			if (isCommentEnd(lines[l])) {
				lines[l] = lines[l] + "\nEOA";
				last_eoa = l;
			}
			if (met) {
				if (isNumber(kw)) {
					lines[l] += "\nEOM";
					met = false;
				} else if (!decl) {
					if (isCommentEnd(line))
						last_eoc = l;
					if (isMethodAttributeStr(kw)) {
						last_eoc = last_boc = -1;
					} else if (isAttributeStr(kw)) {
						if (last_eoc == -1) {
							MLog.putMsg(MLog.PNotice, "attribute keyword outside comment");
							return null;
						}
						lines[last_eoc] += "\nEOD";
						decl = true;
					}
					if (isCommentStart(line)) {
						last_boc = l - 1;
					}
				}
			}
			if ("method".equals(kw)) {
				last_boc = l - 1;
				met = true;
			}
		}
		if (last_eoc < 0)
			last_eoc = last_boc;
		if (!decl && (last_eoc >= 0))
			if (last_eoc < 0) {
				lines[0] = "\nEOD" + lines[0];
			} else {
				if ((last_eoa < 0) || (last_eoa > last_eoc))
					lines[last_eoc] += "\nEOA";
				lines[last_eoc] += "\nEOD";
			}
		String newCode = "";
		for (int l=0; l<lines.length; l++)
			newCode += lines[l] + "\n";
		MLog.putMsg(MLog.PDebug, OldTests.xxx);
		MLog.putMsg(MLog.PDebug, "newCode:\n" + newCode);
		return newCode;
	}
	
	/**
	 * Synchronizes position from original bytecode to
	 * bytecode decorated with {@link #decorate(String)}
	 * method.
	 * 
	 * @param oldCode - original bytecode,
	 * @param newCode - bytecode decorated
	 * 		by {@link #decorate(String)} method,
	 * @param oldPos - position (offset) in original bytecode.
	 * @return position (offset) in decorated bytecode.
	 */
	private static int newPos(String oldCode, String newCode, int oldPos) {
		String oldLines[] = oldCode.split("\n");
		String newLines[] = newCode.split("\n");
		int diff = 0;
		int j=0;
		int lnr = getLineOfOffset(oldCode, oldPos);
		if (lnr >= oldLines.length)
			lnr = oldLines.length - 1;
		for (int i=0; i<=lnr; i++) {
			for (int x=0; x<3; x++) {
				if (j >= newLines.length - 1)
					break;
				if (!oldLines[i].equals(newLines[j])) {
					diff += newLines[j].length() + 1;
					j++;
				}
			}
			if (!oldLines[i].equals(newLines[j]))
				throw new RuntimeException("error in newPos()!");
			j++;
		}
		return oldPos + diff;
	}
	
	/**
	 * Perform basic syntax checking for given bytecode.
	 * Check comment parenthness and apperance of some
	 * keyword (whether they are inside or outside comment).
	 * 
	 * @param code - a String representation of bytecode,
	 * @return <b>true</b> if <code>code</code> is correct
	 * 		enought to attempt searching CodePositions in it,
	 * 		<b>false</b> otherwise.
	 */
	private static boolean checkParenthness(String code) {
		if (code == null)
			return false;
		if (code.indexOf("\nEOD\n") < 0) {
			MLog.putMsg(MLog.PInfo, "no EOD found");
			return false;
		}
		String[] lines = code.split("\n");
		boolean inComment = false;
		boolean inMethodSpec = false;
		for (int l=0; l<lines.length; l++) {
			String line = lines[l];
			String kw = getKeyword(line);
			if (("EOD".equals(line)) || ("EOM".equals(line)))
				inMethodSpec = true;
			if ("method".equals(kw))
				inMethodSpec = false;
			if (isCommentStart(line)) {
				if (inComment) {
					MLog.putMsg(MLog.PInfo, "invalid comment parenthness: /*/*");
					return false;
				}
				inComment = true;
			}
			if (inComment) {
				if (("mthod".equals(kw))
					|| ("class".equals(kw))
					|| ("package".equals(kw))
					|| (isNumber(kw))) {
						MLog.putMsg(MLog.PInfo, "invalid keyword in comment: " + kw);
						return false;
					}
				if (isAttributeStr(kw)) {
					if (isMethodAttributeStr(kw) != inMethodSpec)
						return false;
				}
			} else {
				if (isAttributeStr(kw)) {
					MLog.putMsg(MLog.PInfo, "invalid keyword outside comment");
					return false;
				}
			}
			if (isCommentEnd(line)) {
				if (!inComment) {
					MLog.putMsg(MLog.PInfo, "invalid comment parenthness: */*/");
					return false;
				}
				inComment = false;
			}
		}
		return true;
	}
	
	/**
	 * Returns {@link CodePosition} representing given offset
	 * in given bytecode.
	 * 
	 * @param code - a String representation of bytecode,
	 * @param pos - offset in <code>code</code>.
	 * @return {@link CodePosition} representing logical
	 * 		position in bytecode, related with
	 * 		<code>pos</code> offset in <code>code</code>.
	 */
	public static CodePosition where(String code, int pos) {
		int lnr = getLineOfOffset(code, pos);
		return where(code, lnr, pos - getLineOffset(code, lnr));
	}

	/**
	 * Returns {@link CodePosition} representing given offset
	 * in given bytecode.
	 * 
	 * @param code - a String representation of bytecode,
	 * @param lnr - number of line in <code>code</code>,
	 * @param pos - offset in <code>line</code>.
	 * @return {@link CodePosition} representing logical
	 * 		position in bytecode, related with
	 * 		given offset in <code>code</code>.
	 */
	public static CodePosition where(String code, int lnr, int lpos) {
		if (code.indexOf("\n") < 0) {
			MLog.putMsg(MLog.PInfo, "code too short");
			return null;
		}
		CodePosition cpos = new CodePosition();
		//DONE add end of declarations and end of method marks
		String newCode = decorate(code);
		if (newCode == null)
			return null;
		int pos = getLineOffset(code, lnr) + lpos;
		int pos1 = newPos(code, newCode, pos);
		lnr = getLineOfOffset(newCode, pos1);
		lpos = pos1 - getLineOffset(newCode, lnr);
		//DONE check comments parenthness (/* */) and keywords
		if (!checkParenthness(newCode))
			return null;
		String[] lines = newCode.split("\n");
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
	
	/**
	 * Commits BML changes in bytecode into BCClass.
	 * First, checks that current bytecode is correct,
	 * then parse it, affecting as few elements of BCClass
	 * as it can. Parsing whole class can be uneffective
	 * (slow), so it tries to skip unaffected BML annotations,
	 * comments and methods. It can parse only BML
	 * annotations, not the bytecode itself (bytecode-level
	 * (BCEL's) structures will be unaffected).
	 */
	public void performChanges() {
		correct = true;
		errMsg = "";
		if (goShowDecoratedCode)
			MLog.putMsg(MLog.PInfo, decorate(code));
		//DONE compute positions of affected code
		CodePosition cp_start = where(code, begin);
		CodePosition cp_old = where(oldCode, oldEnd);
		CodePosition cp_new = where(code, end);
		if (cp_old == null)
			if (!checkParenthness(decorate(oldCode)))
				if (cp_start != null) {
					MLog.putMsg(MLog.PNotice,
						"code has just became correct enought"
						+ " to attempt to parse it.");
					cp_old = cp_new;
				}
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
		boolean decl = true;
		boolean mspec = true;
		boolean affd = cp_start.isInClassAttribute();
		int mnr = 0;
		boolean affm = true;
		int inr = 0;
		boolean affi = true;
		int anr = -1;
		boolean affa = true;
		String akw = null;
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
				lines[l] = "[[" + kw + "]]";
				continue;
			}
			// class attributes
			if ("EOD".equals(kw)) {
				if (!affd)
					lines[l] = "\\class attributes unaffected";
				decl = false;
				akw = null;
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
				akw = null;
				continue;
			}
			if (!affm) {
				lines[l] = null;
				continue;
			}
			if ("method".equals(kw)) {
				lines[l] = "[[method header]]";
				mspec = false;
				anr = -1;
				akw = null;
				continue;
			}
			// instructions
			affi = mma || (cp_start.getInstr_nr() <= inr)
				&& ((cp_old.getInstr_nr() >= inr)
					|| (cp_new.getInstr_nr() >= inr)
					|| (cp_old.getInstr_cnt()
						!= cp_new.getInstr_cnt()));
			if (isNumber(kw)) {
				lines[l] = "[[instruction]]";
				if (!affi) {
//					if (mspec) {
//						lines[l] = "\\method specification unaffected";
//					} else {
						lines[l] = "\\instruction unaffected";
//					}
				}
				inr++;
				anr = -1;
				affi = (cp_start.getInstr_nr() <= inr)
				&& ((cp_old.getInstr_nr() >= inr)
					|| (cp_new.getInstr_nr() >= inr)
					|| (cp_old.getInstr_cnt()
						!= cp_new.getInstr_cnt()));
				akw = null;
				continue;
			}
			if (!affi && (!mspec)) {
				lines[l] = null;
				continue;
			}
			// annotations
			affa = mia || (cp_start.getAnnot_nr() <= anr)
				&& ((cp_old.getAnnot_nr() >= anr)
					|| (cp_new.getAnnot_nr() >= anr))
					|| (cp_old.getAnnot_cnt()
						!= cp_new.getAnnot_cnt())
					|| (cp_start.getAnnot_cnt()
						!= cp_old.getAnnot_cnt());
			if (mspec)
				affa = (cp_start.isInMethodSpec())
					|| (cp_old.isInMethodSpec())
					|| (cp_new.isInMethodSpec());
			if (isAttributeStr(kw))
				akw = kw;
			if ("EOA".equals(kw)) {
				if ((anr == -1) && (mspec))
					lines[l] = null;
				if ((anr >= 0) && (!affa)) {
					if (mspec) {
						//XXX this should be updated while adding new nethod attribute.
						if (IDisplayStyle._requires.equals(akw)) {
							lines[l] = "\\method specification unaffected";
						} else {
							throw new RuntimeException("invalid method attribute not detected: " + kw);
						}
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
		shortCode = shortCode.replaceAll("\n *"
				+ Parsing.escape(IDisplayStyle.comment_start), "\n");
		shortCode = shortCode.replaceAll("\n *"
				+ Parsing.escape(IDisplayStyle.comment_next), "\n");
		shortCode = shortCode.replaceAll(
				Parsing.escape(IDisplayStyle.comment_end)
				+ " *\n", "\n");
		if (isCommentStart(shortCode))
			shortCode = shortCode.substring(IDisplayStyle.comment_length);
		while (shortCode.indexOf("\n\n") >= 0)
			shortCode = shortCode.replaceAll("\n\n", "\n");
		last_parsed = shortCode;
		MLog.putMsg(MLog.PInfo, "code to be parsed:\n" + shortCode);
		if (goDisableParser)
			return;
		//DONE create grammar for parsing bytecode
		//DONE check correctness of new code fragment
		if (!correct)
			throw new RuntimeException("error in performChanges()");
		correct = bcc.getParser().parseClass(shortCode, false);
		//DONE and parse it into bcc.
		if (correct)
			bcc.getParser().parseClass(shortCode, true);
	}
	
	/**
	 * Assumes that bytecode has been parsed succesfuly.
	 * It should be called after each
	 * {@link #performChanges()} call, if bytecode is correct.
	 * Calling it for incorrect bytecode may result of ignoring
	 * some errors in next parsing attempt.
	 * This method has been separated from
	 * {@link #performChanges()} method only for test
	 * pusposes, to show {@link CodeFragment}'s state
	 * just after parsing it.
	 */
	public void resetChanges() {
		oldCode = code;
		begin = end = oldEnd = -1;
		toAdd = toRemove = prefix = suffix = null;
		modified = false;
	}
	
	/**
	 * Modifies current bytecode, replacing given fragment
	 * with another String and updating {@link BCClass}.
	 * Either use this or seuqntly:<br>
	 * - {@link #addChange(int, int, String)} (one or more
	 * 		times (for merged changes)),<br>
	 * - {@link #performChanges()},<br>
	 * - {@link #resetChanges()}.
	 * 
	 * @param cfrom - position of first modified character,
	 * @param length - length of removed String,
	 * @param nc - new String added at removed String's
	 * 		position.
	 * @see #addChange(int, int, String)
	 */
	public void modify(int cfrom, int length, String nc) {
		addChange(cfrom, length, nc);
		performChanges();
		MLog.putMsg(MLog.PInfo, toString());
		if (correct)
			resetChanges();
	}
	
	/**
	 * @return a hash code for this editing bytecode
	 * 		(the same result if (but not only if) all
	 * 		fields are the same).
	 */
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

	/**
	 * Displays current state of this bytecode fragment.
	 */
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

	/**
	 * @return current bytecode.
	 */
	public String getCode() {
		return code;
	}

	/**
	 * @return whether current bytecode is correct.
	 * 		It can ignore errors that are far enought from
	 * 		edited fragment (eg. if they were there at the
	 * 		beginnin, or before last {@link #resetChanges()}
	 * 		call.
	 */
	public boolean isCorrect() {
		return correct;
	}

	/**
	 * @return last error message.
	 * 		Currenlty error messages tells only if code were
	 * 		parsed by ANTLR, or was so incorrect that was
	 * 		rejected before passing it to ANTLR.
	 */
	public String getErrMsg() {
		return errMsg;
	}
	
	/**
	 * Searches nearest bytecode (not BML) line above
	 * given one in given bytecode.
	 * For use in code position's synchronization in editors.
	 * 
	 * @param code - a bytecode with BML annotations,
	 * @param lnr - number of line in <code>code</code>.
	 * @return number of nearest line in <code>code</code>
	 * 		above <code>lnr</code>'s that is not a BML
	 * 		annotation's line.
	 */
	public static int goUp(String code, int lnr) {
		String[] lines = code.split("\n");
		if (lnr <= 0)
			return 0;
		if (lnr >= lines.length)
			return lines.length - 1;
		String kw = getKeyword(lines[lnr]);
		for (int l=lnr; l>=0; l--) {
			if (isCommentStart(lines[l]))
				return l;
			if (l == lnr)
				continue;
			kw = getKeyword(lines[l]);
			if ("method".equals(kw) || "EOM".equals(kw)
				|| "EOD".equals(kw) || isNumber(kw))
					return l + 1;
		}
		return 0;
	}
	
	/**
	 * Searches nearest bytecode (not BML) line below
	 * given one in given bytecode.
	 * For use in code position's synchronization in editors.
	 * 
	 * @param code - a bytecode with BML annotations,
	 * @param lnr - number of line in <code>code</code>.
	 * @return number of nearest line in <code>code</code>
	 * 		below <code>lnr</code>'s that is not a BML
	 * 		annotation's line.
	 */
	public static int goDown(String code, int lnr) {
		String[] lines = code.split("\n");
		if (lnr <= 0)
			return 0;
		if (lnr >= lines.length)
			return lines.length - 1;
		String kw = getKeyword(lines[lnr]);
		if ("method".equals(kw) || isNumber(kw))
			return lnr;
		int cnt = lines.length;
		int ret = cnt - 1;
		for (int l=lnr + 1; l<cnt; l++) {
			kw = getKeyword(lines[l]);
			if ("EOM".equals(kw) || "EOD".equals(kw)) {
						ret = l - 1;
						break;
			}
			if (isNumber(kw) || "method".equals(kw)) {
				ret = l;
				break;
			}
		}
		while ((ret > lnr) && ("".equals(lines[ret])))
			ret--;
		return ret;
	}
}
