package annot.textio;

public class CodePosition {

	private String code;
	private int met_nr = -1;
	private int instr_nr = -1;
	private int min_nr = -1;
	private int pc = -1;
	private String keyword;
	private int begin = -1;
	private int end = -1;
	private boolean inComment = false;
	
	public CodePosition(String code) {
		this.code = code;
	}

	public int getBegin() {
		return begin;
	}

	public void setBegin(int begin) {
		this.begin = begin;
	}

	public int getEnd() {
		return end;
	}

	public void setEnd(int end) {
		this.end = end;
	}

	public int getInstr_nr() {
		return instr_nr;
	}

	public void setInstr_nr(int instr_nr) {
		this.instr_nr = instr_nr;
	}

	public void incInstr_nr() {
		this.instr_nr++;
	}

	public String getKeyword() {
		return keyword;
	}

	public void setKeyword(String keyword) {
		this.keyword = keyword;
	}

	public void removeKeyword() {
		this.keyword = null;
	}

	public int getMet_nr() {
		return met_nr;
	}

	public void setMet_nr(int met_nr) {
		this.met_nr = met_nr;
	}

	public void incMet_nr() {
		this.met_nr++;
	}

	public int getMin_nr() {
		return min_nr;
	}

	public void setMin_nr(int min_nr) {
		this.min_nr = min_nr;
	}

	public void incMin_nr() {
		this.min_nr++;
	}

	public int getPc() {
		return pc;
	}

	public void setPc(int pc) {
		this.pc = pc;
	}

	public boolean isInComment() {
		return inComment;
	}

	public void setInComment(boolean inComment) {
		this.inComment = inComment;
	}

	public boolean isInClassAttribute() {
		return met_nr == -1;
	}
	
	public String toString() {
		String str = "";
		str += "[" + met_nr;
		str += ", " + instr_nr;
		str += ", " + min_nr + "] ";
		str += (inComment ? "* " : "  ");
		if (begin > 0) {
			str += "from: " + begin + "(";
			str += code.substring(begin - 1, begin + 1);
			str += ")";
		}
		if ((end > 0) && (end < code.length() - 1)) {
			str += " to: " + end + "(";
			str += code.substring(end - 1, end + 1);
			str += ")";
		}
		if ((begin == 0) && (end == code.length() - 1))
			str += "whole code";
		return str;
	}
}
