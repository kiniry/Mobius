package annot.textio;

/**
 * This class represents a position in bytecode
 * (in its logical representation only).
 * It only stores a couple of values, it doesn't compute
 * anything itself. Contains mainly accessors for these values.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class CodePosition {
  //XXX shouldn't I change fields visibility to public instead of creating
  //    accessors here?
  //XXX shouldn't I at least remove comments from accessors?

  /**
   * The string hash is calculated modulo this number.
   */
  private static final int STRING_HASH_MODULO = 1000000;

  /**
   * The hash is calculated modulo this number.
   */
  private static final int HASH_MODULO = 1000;

  /**
   * The value of the hash for positions inside a method are modified using
   * this number.
   */
  private static final int INMETHOD_HASH_MODIFIER = 17;

  /**
   * The value of the hash for positions inside a class, but before method,
   * are modified using this number.
   */
  private static final int INCLASS_HASH_MODIFIER = 11;

  /**
   * Number of annotations in current comment.
   */
  private int annot_cnt = -1;

  /**
   * Annotation number.
   */
  private int annot_nr = -1;

  /**
   * Contains <code>true</code> when this position is in class attributes
   * section (before first method).
   */
  private boolean inClassAttribute;

  /**
   * Flag set to <code>true</code> iff this position is in method specification.
   */
  private boolean inMethodSpec;

  /**
   * Number of instructions in current method.
   */
  private int instr_cnt = -1;

  /**
   * The instruction number.
   */
  private int instr_nr = -1;

  /**
   * nearest (upside) annotation keyword. Can be anything
   * if this position is outside comment
   */
  private String keyword;

  /**
   * The number of methods in the current class.
   */
  private int met_cnt = -1;

  /**
   * The current method number.
   */
  private int met_nr = -1;

  /**
   * The pc number of current instruction (for debug purpose, display, only).
   */
  private int pc = -1;

  /**
   * A standard contructor.
   */
  public CodePosition() {
  }


  /**
   * Computes sum of character in str (+ 1) modulo
   * {@link CodePosition#STRING_HASH_MODULO}.
   *
   * @param str - any String
   * @return the hash code of this String (the same value for .equal() Strings).
   */
  public static int strHash(final String str) {
    if (str == null) {
      return 0;
    }
    int h = 1;
    for (int i = 0; i  <  str.length(); i++) {
      h = (h + i * str.charAt(i)) % STRING_HASH_MODULO;
    }
    return h;
  }

  /**
   * @return annotation count.
   */
  public int getAnnot_cnt() {
    return this.annot_cnt;
  }

  /**
   * @return current annotation number.
   */
  public int getAnnot_nr() {
    return this.annot_nr;
  }

  /**
   * @return instruction count.
   */
  public int getInstr_cnt() {
    return this.instr_cnt;
  }

  /**
   * @return instruction number.
   */
  public int getInstr_nr() {
    return this.instr_nr;
  }

  /**
   * @return current annotation's keyword. Can return
   *     anything if current position is outside comment.
   */
  public String getKeyword() {
    return this.keyword;
  }

  /**
   * @return method count.
   */
  public int getMet_cnt() {
    return this.met_cnt;
  }

  /**
   * @return current method number.
   */
  public int getMet_nr() {
    return this.met_nr;
  }

  /**
   * @return pc number of current annotaition.
   */
  public int getPc() {
    return this.pc;
  }

  /**
   * @return a hash code for this position in code
   *     (the same result if (but not only if) all
   *     fields are the same).
   */
  public int hash() {
    int h = 0;
    h += this.annot_cnt;
    h += this.instr_cnt;
    h += this.instr_nr;
    h += this.met_cnt;
    h += this.met_nr;
    h += this.annot_nr;
    h += this.pc;
    if (this.inClassAttribute) {
      h += INCLASS_HASH_MODIFIER;
    }
    if (this.inMethodSpec) {
      h += INMETHOD_HASH_MODIFIER;
    }
    h += strHash(this.keyword);
    return h % HASH_MODULO;
  }

  /**
   * Increases instruction number by 1.
   */
  public void incInstr_nr() {
    this.instr_nr++;
  }

  /**
   * Increases current method number by 1.
   */
  public void incMet_nr() {
    this.met_nr++;
  }

  /**
   * Increases current annotation number by 1.
   *
   */
  public void incMin_nr() {
    this.annot_nr++;
  }

  /**
   * @return whether this position is in class attribute
   *     section of bytecode (before first method).
   */
  public boolean isInClassAttribute() {
    return this.inClassAttribute;
  }

  /**
   * @return whether this position is in a method
   * specification.
   */
  public boolean isInMethodSpec() {
    return this.inMethodSpec;
  }

  /**
   * Removes annotation's keyword, setting it to null.
   */
  public void removeKeyword() {
    this.keyword = null;
  }

  /**
   * Sets annotation count.
   *
   * @param pannot_cnt - annotation count value.
   */
  public void setAnnot_cnt(final int pannot_cnt) {
    this.annot_cnt = pannot_cnt;
  }

  /**
   * Sets current annotation number.
   *
   * @param min_nr - new annotation number to be set.
   */
  public void setAnnot_nr(final int min_nr) {
    this.annot_nr = min_nr;
  }

  /**
   * Sets whether this position is in class attribute
   *     section of bytecode (before first method).
   *
   * @param ainClassAttribute - whether this position
   *     is in class attribute section of bytecode.
   */
  public void setInClassAttribute(final boolean ainClassAttribute) {
    this.inClassAttribute = ainClassAttribute;
  }

  /**
   * Sets whether this position is in method specification.
   *
   * @param ainMethodSpec - whether this position
   *     is in method specification.
   */
  public void setInMethodSpec(final boolean ainMethodSpec) {
    this.inMethodSpec = ainMethodSpec;
  }

  /**
   * Sets instruction count.
   *
   * @param ainstr_cnt - instruction count value.
   */
  public void setInstr_cnt(final int ainstr_cnt) {
    this.instr_cnt = ainstr_cnt;
  }

  /**
   * Sets instruction number.
   *
   * @param ainstr_nr - new instruction number to be set.
   */
  public void setInstr_nr(final int ainstr_nr) {
    this.instr_nr = ainstr_nr;
  }

  /**
   * Sets current annotation's keyword.
   *
   * @param akeyword - new keyword value to set.
   */
  public void setKeyword(final String akeyword) {
    this.keyword = akeyword;
  }

  /**
   * Sets method count.
   *
   * @param amet_cnt - method count value to be set.
   */
  public void setMet_cnt(final int amet_cnt) {
    this.met_cnt = amet_cnt;
  }

  /**
   * Sets current method number.
   *
   * @param amet_nr - new method number to be set.
   */
  public void setMet_nr(final int amet_nr) {
    this.met_nr = amet_nr;
  }

  /**
   * Sets pc numner of current annotation.
   *
   * @param apc - new pc number value.
   */
  public void setPc(final int apc) {
    this.pc = apc;
  }

  /**
   * @return a String representation of this bytecode
   *     position.
   */
  @Override
  public String toString() {
    String str = "";
    if (this.met_nr  >= 0) {
      str += "m: " + this.met_nr;
    } else {
      str += "m: -";
    }
    if (this.met_cnt  >= 0) {
      str += " of " + this.met_cnt;
    }
    if (this.instr_nr  >= 0) {
      str += ", i: " + this.instr_nr;
    } else {
      str += ", i: -";
    }
    if (this.pc  >= 0) {
      str += " (pc=" + this.pc + ")";
    }
    if (this.instr_cnt  >= 0) {
      str += " of " + this.instr_cnt;
    }
    if (this.annot_nr  >= 0) {
      str += ", a: " + this.annot_nr;
    }
    if (this.annot_cnt  >= 0) {
      str += " of " + this.annot_cnt;
    }
    if (this.inClassAttribute) {
      str += " c";
    }
    if (this.inMethodSpec) {
      str += " m";
    }
    if (this.keyword != null) {
      str += ", keyword: " + this.keyword;
    }
    str += "  #" + hash();
    return str;
  }
}
