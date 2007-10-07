package annot.textio;

public class CodePosition {

	private String code;
	private int met_nr = -1;
	private int instr_nr = -1;
	private int min_nr = -1;
	private String keyword;
	private boolean inClassAttribute = true;
	
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

	public int getMin_nr() {
		return min_nr;
	}

	public void setMin_nr(int min_nr) {
		this.min_nr = min_nr;
	}

	public void incMin_nr() {
		this.min_nr++;
	}

	public boolean isInClassAttribute() {
		return inClassAttribute;
	}

	public void setInClassAttribute(boolean inClassAttribute) {
		this.inClassAttribute = inClassAttribute;
	}

	public String toString() {
		String str = "";
		str += "[" + met_nr;
		str += ", " + instr_nr;
		str += ", " + min_nr + "] ";
		str += (inClassAttribute ? "c " : "  ");
		if (keyword != null)
			str += " keyword: " + keyword;
		return str;
	}
}
