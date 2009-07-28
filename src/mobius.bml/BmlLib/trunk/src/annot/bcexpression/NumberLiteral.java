package annot.bcexpression;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents an integer literal. Each occurence
 * of the same literal are new NumberLiteral object.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class NumberLiteral extends AbstractIntExpression {

  /**
   * The value of the current literal expression.
   */
  private int value;

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - stream to load from,
   * @param root - expression type (connector).
   * @throws ReadAttributeException - if stream is empty
   *     (less than 4 bytes left).
   * @see BCExpression#BCExpression(AttributeReader, int)
   */
  public NumberLiteral(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor, used eg. by the parser.
   *
   * @param literal the value of the expression
   */
  public NumberLiteral(final int literal) {
    super(Code.INT_LITERAL);
    this.value = literal;
  }

  /**
   * @return JavaType of this expression, that is, JAVA_INT_TYPE.
   */
  @Override
  protected JavaType checkType1() {
    return JavaBasicType.JAVA_INT_TYPE;
  }

  /**
   * @param conf - see {@link BMLConfig}
   * @return String representation of the value of the number
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    return "" + this.value;
  }

  /**
   * Reads the exression from an AttributeReader.
   *
   * @param ar - stream to load from,
   * @param root - connentor (unused).
   * @throws ReadAttributeException - if stream is empty
   *     (less than 4 bytes left).
   */
  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    this.value = ar.readInt();
  }

  /**
   * @return Simple String representation of this
   *     expression, for debugging only.
   */
  @Override
  public String toString() {
    return "" + this.value;
  }

  /**
   * Writes this expression to AttributeWirter.
   *
   * @param aw - stream to save to.
   */
  @Override
  public void write(final AttributeWriter aw) {
    aw.writeByte(Code.INT_LITERAL);
    aw.writeInt(this.value);
  }

  /**
   * @return the value of the literal expression.
   */
  public int getValue() {
    return this.value;
  }
}
