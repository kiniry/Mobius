package annot.bcexpression.formula;

import annot.bcexpression.BCExpression;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents expression of boolean result type
 * and boolean subexpressions result types.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class Formula extends AbstractFormula {

  /**
   * The number of arguments of unary logical operator (i.e. !)
   */
  private static final int UNARY_FORMULA_NOOFARGS = 1;

  /**
   * The number of arguments of innary logical operator (eg. &&, || etc.)
   */
  private static final int BINARY_FORMULA_NOOFARGS = 2;

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - stream to load from,
   * @param root - expression type (connector).
   * @throws ReadAttributeException - if connector + stream
   *     in <code>ar</code> doesn't represent any
   *     formula from this class.
   * @see AbstractFormula#AbstractFormula(AttributeReader, int)
   */
  public Formula(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * Another constructor for 0Arg formula.
   *
   * @param connector - type of expression
   *     (from annot.io.Code interface).
   */
  protected Formula(final int connector) {
    super(connector);
  }

  /**
   * A Constructor for unary formula.
   *
   * @param connector - type of expression
   *     (from annot.io.Code interface),
   * @param subExpr - subexpression.
   */
  public Formula(final int connector, final BCExpression subExpr) {
    super(connector, subExpr);
  }

  /**
   * A constructor for binary formula.
   *
   * @param connector - type of expression
   *     (from annot.io.Code interface),
   * @param left - left subexpression,
   * @param right - right subexrpession.
   */
  public Formula(final int connector, final BCExpression left,
                 final BCExpression right) {
    super(connector, left, right);
  }

  /**
   * Checks if all subexpressions have correct types
   * and return type of this formula (JavaBool).
   *
   * @return JavaBool, or null if this formula is invalid
   *     (if one of it's  subexpression have wrong type
   *     or is invalid).
   */
  @Override
  protected JavaType checkType1() {
    for (int i = 0; i  <  getSubExprCount(); i++) {
      if (getSubExpr(i).getType() != JavaBasicType.JavaBool) {
        return null;
      }
    }
    return JavaBasicType.JavaBool;
  }

  /**
   * Prints this formula to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of formula,
   *     without (block marks (used for line-breaking
   *     by prettyPrinter) and parenthness) at root.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    if (getSubExprCount() == 1) {
      return printRoot(conf) + getSubExpr(0).printCode(conf);
    }
    return getSubExpr(0).printCode(conf) + printRoot(conf) +
      getSubExpr(1).printCode(conf);
  }

  /**
   * Prints formula's connector as a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of formula's connector.
   */
  private String printRoot(final BMLConfig conf) {
    String res = "";
    String surr = " ";
    switch (getConnector()) {
      case Code.AND:
        res = "&&";
        break;
      case Code.OR:
        res = "||";
        break;
      case Code.IMPLIES:
        res = "==>";
        break;
      case Code.NOT:
        res = "!";
        surr = "";
        break;
      case Code.EQUIV:
        res = "<==>";
        break;
      case Code.NOTEQUIV:
        res = "<=!=>";
        break;
      default:
        res = "??";
        break;
    }
    return surr + res + surr;
  }

  /**
   * Reads the formula from an AttributeReader (except
   * connector, thar has been already read and set).
   *
   * @param ar - stream to load from,
   * @param root - connentor.
   * @throws ReadAttributeException - if connector + stream
   *     in <code>ar</code> doesn't represent correct
   *     expression.
   */
  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    if (root == Code.NOT) {
      setSubExprCount(UNARY_FORMULA_NOOFARGS);
      setSubExpr(0, ar.readExpression());
    } else {
      setSubExprCount(BINARY_FORMULA_NOOFARGS);
      setSubExpr(0, ar.readExpression());
      setSubExpr(1, ar.readExpression());
    }
  }

  /**
   * @return Simple String representation of this
   *     formula, for debugging only.
   */
  @Override
  public String toString() {
    if (getSubExprCount() == 1) {
      return printRoot(null) + getSubExpr(0).toString();
    } else {
      return "(" + getSubExpr(0).toString() + printRoot(null) +
        getSubExpr(1).toString() + ")";
    }
  }
}
