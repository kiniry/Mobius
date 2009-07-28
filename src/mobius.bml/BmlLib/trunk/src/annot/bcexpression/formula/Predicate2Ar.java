package annot.bcexpression.formula;

import annot.bcexpression.BCExpression;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents binary predicate of boolean return
 * type and integer subexpressions return types.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class Predicate2Ar extends AbstractFormula {

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - stream to load from,
   * @param root - type of predicate (connector),
   * @throws ReadAttributeException - if connector + stream
   *     in AttributeReader don't represents correct
   *     binary predicate.
   * @see AbstractFormula#AbstractFormula(AttributeReader, int)
   */
  public Predicate2Ar(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor, used eg. in parser.
   *
   * @param connector - type of predicate (connector),
   * @param left - left subexpression,
   * @param right - right subexpression.
   */
  public Predicate2Ar(final int connector, final BCExpression left,
                      final BCExpression right) {
    super(connector, left, right);
  }

  /**
   * Checks if all subexpressions have correct types
   * and return type of this predicate.
   *
   * @return JAVA_BOOLEAN_TYPE, or null if it's invalid
   *     (if one of it's subexpression have wrong type
   *     or is invalid).
   */
  @Override
  protected JavaType checkType1() {
    if (getSubExpr(0).getType().compareTypes(getSubExpr(1).getType()) ==
        JavaType.TYPES_UNRELATED) {
      return null;
    }
    if (getConnector() != Code.EQ && getConnector() != Code.NOTEQ) {
      if (getSubExpr(0).getType() != JavaBasicType.JAVA_INT_TYPE) {
        return null;
      }
    }
    return JavaBasicType.JAVA_BOOLEAN_TYPE;
  }

  /**
   * Prints this predicate to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of this predicate,
   *     without (block marks (used for line-breaking
   *     by prettyPrinter) and parenthness) at root.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    return getSubExpr(0).printCode(conf) + printRoot() +
      getSubExpr(1).printCode(conf);
  }

  /**
   * @return String representation of predicate's connector.
   */
  private String printRoot() {
    switch (getConnector()) {
      case Code.GRT:
        return "  >  ";
      case Code.GRTEQ:
        return "  >= ";
      case Code.LESS:
        return "  <  ";
      case Code.LESSEQ:
        return "  <= ";
      case Code.EQ:
        return " == ";
      case Code.NOTEQ:
        return " != ";
      default:
        return "??";
    }
  }

  /**
   * Reads the predicate from an AttributeReader (except
   * connector, thar has been already read and set).
   *
   * @param ar - stream to load from,
   * @param root - connentor.
   * @throws ReadAttributeException - if connector + stream
   *     in <code>ar</code> doesn't represent correct
   *     binary predicate.
   */
  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    setSubExprCount(2);
    setSubExpr(0, ar.readExpression());
    setSubExpr(1, ar.readExpression());
  }

  /**
   * @return Simple String representation of this
   *     predicate, for debugging only.
   */
  @Override
  public String toString() {
    if (getSubExprCount() == 1) {
      return printRoot() + getSubExpr(0).toString();
    } else {
      return getSubExpr(0).toString() + printRoot() + getSubExpr(1).toString();
    }
  }

}
