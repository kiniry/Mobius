package annot.bcexpression;

import annot.bcexpression.formula.QuantifiedFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents bound variable. It represents
 * a variable, not it's ocurence, eg. in 'forall a ; a  >  0'
 * both occurences of 'a' are the same object.<br>
 * XXX Bound variable names cannot shadow each other (parser).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BoundVar extends BCExpression {

  /**
   * Display style (true for variable name, false
   * for 'var['+index+']'.
   */
  public static final boolean goWriteVarNames = true;

  /**
   * Variable id. In each place in expression, all visible
   * bound variables have distinct ids.
   */
  private final int index;

  /**
   * Quantifier where this variable was declared.
   */
  private final QuantifiedFormula qf;

  /**
   * Declared type of variable.
   */
  private final JavaType type;

  /**
   * variable name.
   */
  private String vname;

  /**
   * A constructor for use in quantifier only.
   * Inside quantified expression use
   * {@link #getBoundVar(AttributeReader)} instead.
   *
   * @param jt - declared type of variable,
   * @param anindex - variable id,
   * @param aqf - quantifier, where it is declared,
   * @param avname - variable name (can be null).
   */
  public BoundVar(final JavaBasicType jt, final int anindex,
                  final QuantifiedFormula aqf, final String avname) {
    super(Code.BOUND_VAR);
    this.type = jt;
    this.index = anindex;
    this.qf = aqf;
    setVname(avname);
  }

  /**
   * Use this to get proper instance while reading occurence
   * (not declaration) of bound variable in an expression.
   *
   * @param ar - stram to read variable id from.
   * @return proper bound variable (declared before,
   *     at quantifier)
   * @throws ReadAttributeException - if <code>ar</code>
   *     contains invalid variable index.
   */
  public static BoundVar getBoundVar(final AttributeReader ar)
    throws ReadAttributeException {
    final int i = ar.readShort();
    return ar.getBvar(i);
  }

  /**
   * Checks if all subexpression have
   * correct types and return type of this expression.
   *
   * @return JavaType of result of this exrpession,
   *     or null if it's invalid (if one of it's
   *     subexpression have wrong type or is invalid).
   */
  @Override
  protected JavaType checkType1() {
    return this.type;
  }

  /**
   * @return quantified formula where this variable
   *     was declared.
   */
  public QuantifiedFormula getQf() {
    return this.qf;
  }

  @Override
  public JavaType getType1() {
    return this.type;
  }

  /**
   * @return variable name, or null if it is unknown
   *     (eg. some old .class file formats don't support
   *     bound variable names).
   */
  public String getVname() {
    return this.vname;
  }

  /**
   * Displays expression to a String.
   *
   * @param conf - see {@link BMLConfig}.
   * @return String representation of expression,
   *     without (block marks (used for line-breaking
   *     by prettyPrinter) and parenthness) at root.
   * @see BCExpression#printCode1(BMLConfig)
   */
  @Override
  public String printCode1(final BMLConfig conf) {
    final String n = getVname();
    if (n != null) {
      return "" + n;
    }
    return "var_" + this.index;
  }

  /**
   * Sets a variable name.
   *
   * @param avname - variable name to be set.
   */
  public void setVname(final String avname) {
    this.vname = avname;
  }

  /**
   * @return Simple String representation of this
   *     expression, for debugging only.
   */
  @Override
  public String toString() {
    return "var[" + this.index + "]";
  }

  /**
   * Writes this expression to AttributeWirter.
   *
   * @param aw - stream to save to.
   */
  @Override
  public void write(final AttributeWriter aw) {
    aw.writeByte(Code.BOUND_VAR);
    aw.writeShort(this.index);
  }

}
