package annot.bcexpression.formula;

import java.util.Iterator;
import java.util.Vector;

import annot.bcexpression.BCExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

/**
 * This class represents a quantifier with bound variable
 * declarations and formula.<br>
 * XXX Bound variable names cannot shadow each other (parser).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class QuantifiedFormula extends AbstractFormula {

  /**
   * The text of the \exists quantifier keyword.
   */
  private static final String EXISTS_KEYWORD_TEXT = "\\exists";

  /**
   * The text of the \forall quantifier keyword.
   */
  private static final String FORALL_KEYWORD_TEXT = "\\forall";

  /**
   * Vector of bound variables.
   */
  private Vector < BoundVar >  vars;

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - stream to load from,
   * @param root - quantifier type (connector).
   * @throws ReadAttributeException - if connector + stream
   *     in <code>ar</code> doesn't represent correct
   *     quantified expression.
   * @see AbstractFormula#AbstractFormula(AttributeReader, int)
   */
  public QuantifiedFormula(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor, used by parser. After creating
   * QuantifiedFormula this way, you must add all it's
   * bound variables and set it's formula, before using
   * this expression.
   *
   * @param connector - type of quantifier
   *     (eg. Code.EXISTS, Code.FORALL).
   */
  public QuantifiedFormula(final int connector) {
    super(connector);
  }

  /**
   * Adds given bound variable to this formula.
   * This should be called after creating QuantifiedFormula
   * using {@link #QuantifiedFormula(int)} constructor,
   * but before setting its formula.
   *
   * @param bv - bound variable to be added. It should
   *     be a newly created variable, not recived using
   *     {@link BoundVar#getBoundVar(AttributeReader)}.
   */
  public void addVariable(final BoundVar bv) {
    if (getSubExpr(0) != null) {
      throw new RuntimeException("formula is already set!");
    }
    this.vars.add(bv);
  }

  /**
   * Checks if subexpression has correct type
   * and return type of this expression.
   *
   * @return JAVA_BOOLEAN_TYPE or null if it's invalid
   *     (if it's subexpression have wrong type
   *     or is invalid).
   */
  @Override
  protected JavaType checkType1() {
    if (getSubExpr(0).getType() != JavaBasicType.JAVA_BOOLEAN_TYPE) {
      return null;
    }
    return JavaBasicType.JAVA_BOOLEAN_TYPE;
  }

  /**
   * Changes connector between new ones (for new .class file
   * format, with bound variable names) and old one,
   * depending on {@link BoundVar#goWriteVarNames} flag.
   *
   * @return corrected connector.
   */
  private int chkConnector() {
    if (BoundVar.goWriteVarNames) {
      if (getConnector() == Code.FORALL) {
        return Code.FORALL_WITH_NAME;
      }
      if (getConnector() == Code.EXISTS) {
        return Code.EXISTS_WITH_NAME;
      }
    } else {
      if (getConnector() == Code.FORALL_WITH_NAME) {
        return Code.FORALL;
      }
      if (getConnector() == Code.EXISTS_WITH_NAME) {
        return Code.EXISTS;
      }
    }
    return getConnector();
  }

  /**
   * @return Number of variables bound by this quantifier.
   */
  public int getLength() {
    return this.vars.size();
  }

  /**
   * @param index - index of bound variable bound by this
   *     quantifier, from left to right, with 0 for
   *     the left-most bound variable of this formula.
   * @return Bound variable at given index.
   */
  public BoundVar getVar(final int index) {
    return this.vars.elementAt(index);
  }

  /**
   * Initialize private fields of this subclass.
   */
  @Override
  protected void init() {
    setSubExprCount(1);
    this.vars = new Vector < BoundVar > ();
  }

  /**
   * Prints quantifier with its formula to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of expression,
   *     without (block marks (used for line-breaking
   *     by prettyPrinter) and parenthness) at root.
   */
  @Override
  protected String printCode1(final BMLConfig conf) {
    String code = printRoot();
    code += DisplayStyle.BLOCK_EXPR_START;
    final Iterator < BoundVar >  iter = this.vars.iterator();
    while (iter.hasNext()) {
      final BoundVar bv = iter.next();
      final JavaBasicType jbt = (JavaBasicType) bv.getType();
      code += " " + jbt.printCode1(conf); // !
      code += " " + bv.printCode1(conf); // !
    }
    code += "; ";
    code += DisplayStyle.BLOCK_EXPR_END;
    String str = getSubExpr(0).printCode(conf);
    if (DisplayStyle.DISPLAY_3ARG_QUANTIFIERS) {
      str = str.substring(1, str.length() - 1);
    }
    code += str;
    return code;
  }

  /**
   * @return String representation of quantifier
   *     (connector)
   */
  private String printRoot() {
    switch (getConnector()) {
      case Code.FORALL:
      case Code.FORALL_WITH_NAME:
        return FORALL_KEYWORD_TEXT;
      case Code.EXISTS:
      case Code.EXISTS_WITH_NAME:
        return EXISTS_KEYWORD_TEXT;
      default:
        return "?";
    }
  }

  /**
   * Reads the bound variable declarations and quantified
   * formula from an AttributeReader.
   *
   * @param ar - stream to load from,
   * @param root - connentor (quantifier).
   * @throws ReadAttributeException - if connector + stream
   *     in <code>ar</code> doesn't represent correct
   *     quantified expression.
   */
  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    final int n = ar.readByte();
    final int bvc = ar.getBvarCount();
    for (int i = 0; i  <  n; i++) {
      final BCExpression expr = ar.readExpression();
      if (!(expr instanceof JavaBasicType)) {
        throw new ReadAttributeException("JavaType expected, read " +
                                         expr.getClass().toString());
      }
      final JavaBasicType jt = (JavaBasicType) expr;
      final BoundVar bv = new BoundVar(jt, bvc + i, this, null);
      if (root == Code.FORALL_WITH_NAME || root == Code.EXISTS_WITH_NAME) {
        final int cpIndex = ar.readShort();
        if (cpIndex != 0) { // ?
          final String vname = ar.findString(cpIndex);
          bv.setVname(vname);
        }
      }
      ar.getBvars().add(bv);
      this.vars.add(bv);
    }
    setSubExpr(0, ar.readExpression());
    for (int i = 0; i  <  n; i++) {
      ar.getBvars().remove(ar.getBvarCount() - 1);
    }
  }

  /**
   * Sets a quantified formula. This should be called after
   * all bound variables have been added, but before using
   * this expression.
   *
   * @param expression - formula to be set.
   */
  public void setFormula(final BCExpression expression) {
    if (getSubExpr(0) != null) {
      throw new RuntimeException("formula is already set!");
    }
    setSubExpr(0, expression);
  }

  /**
   * @return Simple String representation of this
   *     expression, for debugging only.
   */
  @Override
  public String toString() {
    String code = printRoot();
    final Iterator < BoundVar >  iter = this.vars.iterator();
    while (iter.hasNext()) {
      code += " " + iter.next().toString();
    }
    code += " " + getSubExpr(0).toString();
    return code;
  }

  /**
   * Writes this expression to AttributeWirter.
   *
   * @param aw - stream to save to.
   */
  @Override
  public void write(final AttributeWriter aw) {
    final int conn = chkConnector();
    aw.writeByte(conn);
    aw.writeByte(this.vars.size());
    final Iterator < BoundVar >  iter = this.vars.iterator();
    while (iter.hasNext()) {
      final BoundVar bv = iter.next();
      bv.checkType().write(aw);
      if (BoundVar.goWriteVarNames) {
        final String vname = bv.getVname();
        if (vname == null) {
          aw.writeShort(0);
        } else {
          final int index = aw.findConstant(vname);
          aw.writeShort(index);
        }
      }
    }
    writeSubExpressions(aw);
  }

}
