package annot.bcexpression.formula;

import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.Code;
import annot.textio.BMLConfig;

/**
 * This class represents 0Arg predicate, that is, TRUE
 * and FALSE predicates only.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class Predicate0Ar extends AbstractFormula {

  /**
   * Predicate value (true for 'true' predicate, and
   * false for 'false' predicate).
   */
  private final boolean value;

  /**
   * A standard constructor.
   *
   * @param avalue - whether constructed object should be
   *     a 'true' predicate.
   */
  public Predicate0Ar(final boolean avalue) {
    super(avalue ? Code.TRUE : Code.FALSE);
    this.value = avalue;
  }

  /**
   * A constructor from AttributeReader.
   *
   * @param root - expression's connector (opcode).
   */
  public Predicate0Ar(final int root) {
    super(root);
    this.value = root == Code.TRUE;
  }

  /**
   * @return JavaType of this predicate, that is, JAVA_BOOLEAN_TYPE.
   */
  @Override
  protected JavaType checkType1() {
    return JavaBasicType.JAVA_BOOLEAN_TYPE;
  }

  /**
   * Prints expression to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of this predicate:
   *     "true" for TRUE, and "false" for FALSE.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    return "" + this.value;
  }

  /**
   * @return simple String representation of this
   *     predicate, for debugging only.
   */
  @Override
  public String toString() {
    return "" + this.value;
  }

  /**
   * @return the value of the constant (i.e. <code>true</code> or
   *   <code>false</code>)
   */
  public boolean getValue() {
    return value;
  }
}
