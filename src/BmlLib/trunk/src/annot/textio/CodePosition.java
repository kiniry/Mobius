package annot.textio;

/**
 * This class represents a position in bytecode (in it's logical representation
 * only). It only stores a couple of values, it doesn't compute anything itself.
 * Contains mainly accessors for this values.
 * 
 * @author tomekb
 */
public class CodePosition {
	// XXX shouldn't I change fields visibility to public instead of creating
	// accessors here?
	// XXX shouldn't I at least remove comments from accessors?

	/**
	 * number of methods in class
	 */
	private int met_cnt = -1;

	/**
	 * number of annotations in current comment
	 */
	private int annot_cnt = -1;

	/**
	 * number of instructions in current method
	 */
	private int instr_cnt = -1;

	/**
	 * method number
	 */
	private int met_nr = -1;

	/**
	 * instruction number
	 */
	private int instr_nr = -1;

	/**
	 * pc number of current instruction (for debug purpose (display) only)
	 */
	private int pc = -1;

	/**
	 * annotation number
	 */
	private int annot_nr = -1;

	/**
	 * nearest (upside) annotation keyword. Can be anything if this position is
	 * outside comment
	 */
	private String keyword;

	/**
	 * wether this position is in class attributes section (before first
	 * method), or not
	 */
	private boolean inClassAttribute = false;

	/**
	 * wether this position is in method specification or not
	 */
	private boolean inMethodSpec = false;

	/**
	 * A standard contructor.
	 */
	public CodePosition() {
	}

	/**
	 * @return instruction number.
	 */
	public int getInstr_nr() {
		return instr_nr;
	}

	/**
	 * Sets instruction number.
	 * 
	 * @param instr_nr -
	 *            new instruction number to be set.
	 */
	public void setInstr_nr(int instr_nr) {
		this.instr_nr = instr_nr;
	}

	/**
	 * Increases instruction number by 1.
	 */
	public void incInstr_nr() {
		this.instr_nr++;
	}

	/**
	 * @return current annotation's keyword. Can return anything if current
	 *         position is outside comment.
	 */
	public String getKeyword() {
		return keyword;
	}

	/**
	 * Sets current annotation's keyword.
	 * 
	 * @param keyword -
	 *            new keyword value to set.
	 */
	public void setKeyword(String keyword) {
		this.keyword = keyword;
	}

	/**
	 * Removes annotation's keyword, setting it to null.
	 */
	public void removeKeyword() {
		this.keyword = null;
	}

	/**
	 * @return current method number.
	 */
	public int getMet_nr() {
		return met_nr;
	}

	/**
	 * Sets current method number.
	 * 
	 * @param met_nr -
	 *            new method number to be set.
	 */
	public void setMet_nr(int met_nr) {
		this.met_nr = met_nr;
	}

	/**
	 * Increases current method number by 1.
	 */
	public void incMet_nr() {
		this.met_nr++;
	}

	/**
	 * @return current annotation number.
	 */
	public int getAnnot_nr() {
		return annot_nr;
	}

	/**
	 * Sets current annotation number.
	 * 
	 * @param min_nr -
	 *            new annotation number to be set.
	 */
	public void setAnnot_nr(int min_nr) {
		this.annot_nr = min_nr;
	}

	/**
	 * Increases current annotation number by 1.
	 * 
	 */
	public void incMin_nr() {
		this.annot_nr++;
	}

	/**
	 * @return wether this position is in class attribute section of bytecode
	 *         (before first method).
	 */
	public boolean isInClassAttribute() {
		return inClassAttribute;
	}

	/**
	 * Sets wether this position is in class attribute section of bytecode
	 * (before first method).
	 * 
	 * @param inClassAttribute -
	 *            wether this position is in class attribute section of
	 *            bytecode.
	 */
	public void setInClassAttribute(boolean inClassAttribute) {
		this.inClassAttribute = inClassAttribute;
	}

	/**
	 * @return method count.
	 */
	public int getMet_cnt() {
		return met_cnt;
	}

	/**
	 * Sets method count.
	 * 
	 * @param met_cnt -
	 *            method count value to be set.
	 */
	public void setMet_cnt(int met_cnt) {
		this.met_cnt = met_cnt;
	}

	/**
	 * @return annotation count.
	 */
	public int getAnnot_cnt() {
		return annot_cnt;
	}

	/**
	 * Sets annotation count.
	 * 
	 * @param annot_cnt -
	 *            annotation count value.
	 */
	public void setAnnot_cnt(int annot_cnt) {
		this.annot_cnt = annot_cnt;
	}

	/**
	 * @return pc number of current annotaition.
	 */
	public int getPc() {
		return pc;
	}

	/**
	 * Sets pc numner of current annotation.
	 * 
	 * @param pc -
	 *            new pc number value.
	 */
	public void setPc(int pc) {
		this.pc = pc;
	}

	/**
	 * @return instruction count.
	 */
	public int getInstr_cnt() {
		return instr_cnt;
	}

	/**
	 * Sets instruction count.
	 * 
	 * @param instr_cnt -
	 *            instruction count value.
	 */
	public void setInstr_cnt(int instr_cnt) {
		this.instr_cnt = instr_cnt;
	}

	/**
	 * @return wether this position is in a method specification.
	 */
	public boolean isInMethodSpec() {
		return inMethodSpec;
	}

	/**
	 * Sets wether this position is in method specification.
	 * 
	 * @param inMethodSpec -
	 *            wether this position is in method specification.
	 */
	public void setInMethodSpec(boolean inMethodSpec) {
		this.inMethodSpec = inMethodSpec;
	}

	/**
	 * Computes sum of character in str (+ 1) modulo 1000000.
	 * 
	 * @param str -
	 *            any String
	 * @return Hash code of this String (the same value for .equal() Strings).
	 */
	public static int StrHash(String str) {
		if (str == null)
			return 0;
		int h = 1;
		for (int i = 0; i < str.length(); i++)
			h = (h + i * (str.charAt(i))) % 1000000;
		return h;
	}

	/**
	 * @return a hash code for this position in code (the same result if (but
	 *         not only if) all fields are the same).
	 */
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

	/**
	 * @return a String representation of this bytecode position.
	 */
	@Override
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
