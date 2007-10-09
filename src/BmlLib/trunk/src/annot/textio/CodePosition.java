package annot.textio;

public class CodePosition {

	private String code;
	private int met_cnt = -1;
	private int annot_cnt = -1;
	private int instr_cnt = -1;
	private int met_nr = -1;
	private int instr_nr = -1;
	private int pc = -1;
	private int annot_nr = -1;
	private String keyword;
	private boolean inClassAttribute = false;
	private boolean inMethodSpec = false;
	
	public CodePosition(String code) {
		this.code = code;
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

	public int getAnnot_nr() {
		return annot_nr;
	}

	public void setAnnot_nr(int min_nr) {
		this.annot_nr = min_nr;
	}

	public void incMin_nr() {
		this.annot_nr++;
	}

	public boolean isInClassAttribute() {
		return inClassAttribute;
	}

	public void setInClassAttribute(boolean inClassAttribute) {
		this.inClassAttribute = inClassAttribute;
	}

	public int getMet_cnt() {
		return met_cnt;
	}

	public void setMet_cnt(int met_cnt) {
		this.met_cnt = met_cnt;
	}

	public int getAnnot_cnt() {
		return annot_cnt;
	}

	public void setAnnot_cnt(int annot_cnt) {
		this.annot_cnt = annot_cnt;
	}

	public int getPc() {
		return pc;
	}

	public void setPc(int pc) {
		this.pc = pc;
	}

	public int getInstr_cnt() {
		return instr_cnt;
	}

	public void setInstr_cnt(int instr_cnt) {
		this.instr_cnt = instr_cnt;
	}

	public boolean isInMethodSpec() {
		return inMethodSpec;
	}

	public void setInMethodSpec(boolean inMethodSpec) {
		this.inMethodSpec = inMethodSpec;
	}

	public static int StrHash(String str) {
		if (str == null)
			return 0;
		int h = 1;
		for (int i=0; i<str.length(); i++)
			h = (h + i * (int)(str.charAt(i))) % 1000000;
		return h;
	}
	
	public int hash() {
		int h = 0;
		h += annot_cnt;
		h += instr_cnt;
		h += instr_nr;
		h += met_cnt;
		h += met_nr;
		h += annot_nr;
		h += pc;
		if (inClassAttribute)
			h += 11;
		if (inMethodSpec)
			h += 17;
		h += StrHash(keyword);
		return h % 1000;
	}

	public String toString() {
		String str = "";
		if (met_nr >= 0) {
			str += "m: " + met_nr;
		} else {
			str += "m: -";
		}
		if (met_cnt >= 0)
			str += " of " + met_cnt;
		if (instr_nr >= 0) {
			str += ", i: " + instr_nr;
		} else {
			str += ", i: -";
		}
		if (pc >= 0)
			str += " (pc=" + pc + ")";
		if (instr_cnt >= 0)
			str += " of " + instr_cnt;
		if (annot_nr >= 0)
			str += ", a: " + annot_nr;
		if (annot_cnt >= 0)
			str += " of " + annot_cnt;
		if (inClassAttribute)
			str += " c";
		if (inMethodSpec)
			str += " m";
		if (keyword != null)
			str += ", keyword: " + keyword;
		str += "  #" + hash();
		return str;
	}
}
