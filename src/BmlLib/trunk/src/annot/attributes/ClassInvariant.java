package annot.attributes;

import org.antlr.runtime.RecognitionException;

import annot.bcclass.BCClass;
import annot.bcexpression.ExpressionRoot;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Predicate0Ar;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;
import annot.textio.Parsing;

/**
 * This class represents class invariant attribute.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class ClassInvariant extends ClassAttribute implements IBCAttribute {

  /**
   * The flag which contains the access flags for the current class
   * invariant.
   */
  private int access_flags;

  /**
   * BCClass contaning this attribute.
   */
  private final BCClass bcc;

  /**
   * The invariant formula.
   */
  private final ExpressionRoot < AbstractFormula >  invariant;

  /**
   * The flag which is <code>true</code> in case the invariant is
   * an instance invariant and <code>false</code> otherwise.
   */
  private boolean isInstance;

  /**
   * A Constructor from BCClass and AbstractFormula.
   *
   * @param abcc - BCClass containing this invariant,
   * @param invariant - a invariant formula.
   * @param instanceflag - <code>true</code> in case the invariant is an
   *   instance invariant
   */
  public ClassInvariant(final BCClass abcc, final AbstractFormula invariant,
                        final boolean instanceflag) {
    this.bcc = abcc;
    this.invariant = new ExpressionRoot < AbstractFormula > (this, invariant);
    this.isInstance = instanceflag;
    commitInstanceFlag();
  }

  /**
   * A constructor from attributeReader, for use in class
   * loading only.
   *
   * @param classRepresentation - BCClass containing this invariant,
   * @param ar - {@link AttributeReader} to load invariant from, it is
   *   in a position right after the length field of the attribute
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent correct
   *     class invariant.
   */
  public ClassInvariant(final BCClass classRepresentation,
                        final AttributeReader ar)
    throws ReadAttributeException {
    this.bcc = classRepresentation;
    this.access_flags = ar.readShort();
    this.isInstance = (this.access_flags & AttributeFlags.ACC_STATIC) == 0;
    this.invariant = new ExpressionRoot < AbstractFormula > (this,
        ar.readFormula());
  }

  /**
   * Creates empty invariant (with formula 'true').
   *
   * @param abcc - BCClass containing this invariant.
   * @param instanceflag - <code>true</code> in case the invariant is an
   *   instance invariant
   */
  public ClassInvariant(final BCClass abcc, final boolean instanceflag) {
    this.bcc = abcc;
    this.invariant = new ExpressionRoot < AbstractFormula > (this,
        new Predicate0Ar(true));
    this.isInstance = instanceflag;
    commitInstanceFlag();
  }

  /**
   * This method propagates the {@link #isInstance} flag to the
   * access_flags field.
   */
  private void commitInstanceFlag() {
    if (!this.isInstance) {
      this.access_flags = this.access_flags | AttributeFlags.ACC_STATIC;
    }
  }

  /**
   * @return the access flags for the current invariant
   */
  public int getAccessFlags() {
    return this.access_flags;
  }

  @Override
  public ExpressionRoot[] getAllExpressions() {
    final ExpressionRoot[] all = new ExpressionRoot[1];
    all[0] = this.invariant;
    return all;
  }

  /**
   * @return nameIndex of BCEL's Unknown
   *     attribute it represents.
   */
  public int getIndex() {
    return this.bcc.getCp().findConstant(DisplayStyle.INVARIANTS_ATTR);
  }

  /**
   * @return the invariant formula.
   */
  public AbstractFormula getInvariant() {
    return this.invariant.getExpression();
  }

  /**
   * @return Unknown (BCEL) attribute name.
   */
  public String getName() {
    return DisplayStyle.INVARIANTS_ATTR;
  }

  /**
   * Return the information if the invariant is instance/static
   *
   * @return <code>true</code> in case the invariant is an instance
   *   invariant, <code>false</code> otherwise
   */
  public boolean isInstance() {
    return this.isInstance;
  }

  /**
   * Replaces this annotation with the one parsed from
   * given String.
   *
   * @param code - correct code of class invariant
   *     to replace with.
   * @throws RecognitionException - if <code>code</code>
   *     is not correct class invariant's code.
   */
  @Override
  public void parse(final String code) throws RecognitionException {
    parse(this.bcc, null, null, -1, code);
  }

  /**
   * Prints the code of the annotation to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of this invariant.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    final String header = this.isInstance ? DisplayStyle._classInvariant :
                                            DisplayStyle._staticInvariant;
    final String code = this.invariant.printLine(conf, header);
    return "\n" + Parsing.addComment(code);
  }

  /**
  * Removes this annotation.
  */
  @Override
  public void remove() {
    this.bcc.remove(getAccessFlags());
  }

  /**
   * Replaces existing class invariant in given
   * BCClass with this attribute.
   *
   * @param abcc - BCClass to place this attribute as it's
   *     class invariant.
   */
  @Override
  public void replace(final BCClass abcc) {
    abcc.setInvariant(this);
  }

  /**
   * Replaces this annotation with a given one, updating
   * nessesery references in BCClass.
   *
   * @param pa - annotation to replace with.
   */
  @Override
  public void replaceWith(final BCPrintableAttribute pa) {
    this.bcc.setInvariant((ClassInvariant) pa);
  }

  /**
   * Saves this annotation to BCEL's Unknown attribute,
   * using attributeWriter.
   * @param aw - stream to save to.
   */
  public void save(final AttributeWriter aw) {
    aw.writeShort(this.access_flags);
    this.invariant.write(aw);
  }

  /**
   * @return Simple string represenatations of attribute,
   *     for use in debugger only.
   */
  @Override
  public String toString() {
    if (this.isInstance) {
      return "invariant";
    } else {
      return "class invariant";
    }
  }
}
