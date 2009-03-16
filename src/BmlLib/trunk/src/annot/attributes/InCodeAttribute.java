package annot.attributes;

import org.antlr.runtime.RecognitionException;
import org.apache.bcel.generic.InstructionHandle;

import annot.bcclass.BCMethod;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents single annotations attached to
 * instructionHandle of an bytecode instruction.
 * (on or more InCodeAttribute per one bytecode instruction)
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class InCodeAttribute extends BCPrintableAttribute implements
    Comparable < InCodeAttribute >  {

  /**
   * InstructionHandle of bytecode instruction that this
   * annotation is attached to.
   * Changed from pc number of instruction to avoid
   * desynchronization after inserting / deleting bytecode
   * instructions above.
   */
  private InstructionHandle ih;

  /**
   * The method containing this annotation.
   */
  private final BCMethod method;

  /**
   * This number is responsible for annotation ordering
   * within single bytecode instruction.
   * Multiple annotations can be attached to one instruction.
   * They are sorted by thier minor number and displayed
   * in this order.
   */
  private int minor;

  /**
   * A standard constructor.
   *
   * @param m - BCMethod containing this annotation,
   * @param a_ih - instructionHandle of bytecode instruction
   *     that this annotation should be attached to,
   * @param a_minor - minor number of annotation, responsible
   *     for annotation ordering within single instruction.
   */
  public InCodeAttribute(final BCMethod m,
                         final InstructionHandle a_ih,
                         final int a_minor) {
    this.method = m;
    this.ih = a_ih;
    this.minor = a_minor;
  }

  /**
   * A constructor for tests only. It can be used only
   * when we are sure that bytecode itself won't change.
   *
   * @param m - BCMethod containing this annotation,
   * @param pc - pc number of bytecode instruction that
   *     this annotation should be attached to. You should
   *     be sure that instruction of that pc really
   *     exists in given method.
   * @param minor - minor number of annotation, responsible
   *     for annotation ordering within single instruction.
   */
  @Deprecated
  public InCodeAttribute(final BCMethod m, final int pc, final int minor) {
    this(m, m.findAtPC(pc), minor);
  }

  /**
   * @return annotation's type id, from AType interface.
   */
  protected abstract int aType();

  /**
   * compares this annotation to given one in order they
   * should appead in String representation of a method.
   * Both annotations should be from the same method.
   * @param o - annotation to compare to.
   * @return a positive integer if <code>o</code> is above
   *     this annotation in String representation of method,
   *     a negative integer if <code>o</code> is below,
   *     and zero if <code>o</code> is the same annotation.
   */
  public int compareTo(final InCodeAttribute o) {
    final int pc = getPC();
    final int opc = o.getPC();
    if (pc == opc) {
      if (this.minor == o.minor) {
        return 0;
      } else {
        return this.minor - o.minor;
      }
    } else {
      return pc - opc;
    }
  }

  /**
   * @return instructionHandle of instruction this annotation
   *     is attached to.
   */
  public InstructionHandle getIh() {
    return this.ih;
  }

  /**
   * @return BCMethod containing this annotation.
   */
  public BCMethod getMethod() {
    return this.method;
  }

  /**
   * @return minor number of this annotation, used for
   *     ordering annotations within the same bytecode
   *     instruction.
   */
  public int getMinor() {
    return this.minor;
  }

  /**
   * Computes pc numbers for each bytecode instruction of
   * a method containing this annotation and returns,
   * and returns pc number of instruction this annotation
   * is attached to.
   *
   * @return pc number of this annotation's
   *     bytecode instruction.
   */
  public int getPC() {
    return this.method.getPC(this.ih);
  }

  /**
   * Loads annotation's content from AttributeReader.
   *
   * @param ar - stream to load from.
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent correct
   *     annotation.
   */
  protected abstract void load(AttributeReader ar)
    throws ReadAttributeException;

  /**
   * Replaces this annotation with the one parsed from
   * given String.
   *
   * @param code - correct code of annotation
   *     to replace with.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct annotation's code.
   */
  @Override
  public void parse(final String code) throws RecognitionException {
    parse(this.method.getBcc(), this.method, this.ih, this.minor, code);
  }

  /**
   * This method should simply print annotation to a string.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of annotation.
   */
  @Override
  protected abstract String printCode1(BMLConfig conf);

  /**
   * Removes this annotation.
   */
  @Override
  public void remove() {
    getMethod().getAmap().removeAttribute(this);
  }

  /**
   * Replaces this annotation with a given one, updating
   * nessesery references in BCAttributeMap in BCMethod.
   *
   * @param pa - annotation to replace with.
   */
  @Override
  public void replaceWith(final BCPrintableAttribute pa) {
    final InCodeAttribute ica = (InCodeAttribute) pa;
    if (ica.ih == null) {
      ica.ih = this.ih;
      ica.minor = this.minor;
    }
    this.method.getAmap().replaceAttribute(this, ica);
  }

  /**
   * Saves annotation content using AttributeWriter.
   *
   * @param aw - stream to save to.
   */
  protected abstract void saveSingle(AttributeWriter aw);

  /**
   * Sets instructionHandle parameter.
   *
   * @param ih - new instruction handle.
   */
  public void setIh(final InstructionHandle ih) {
    this.ih = ih;
  }

  /**
   * Sets minor number.
   *
   * @param minor - new minor number value to set.
   */
  protected void setMinor(final int minor) {
    this.minor = minor;
  }

}
