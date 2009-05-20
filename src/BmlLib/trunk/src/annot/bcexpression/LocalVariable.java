package annot.bcexpression;

import org.apache.bcel.generic.LocalVariableGen;

import annot.bcclass.BCMethod;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents method's local variable.
 * One <code>LocalVariable</code> per one local variable.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class LocalVariable extends BCExpression {

  /**
   * BCEL's representation of this variable.
   */
  private final LocalVariableGen bcelLvGen;

  /**
   * Number (index) of this variable
   * in method <code>m</code>.
   */
  private final int lvar_id;

  /**
   * Method in with this variable has been declared.
   */
  private final BCMethod m;

  /**
   * Name of this variable.
   */
  private final String name;

  /**
   * Type of this variable.
   */
  private final JavaType type;

  /**
   * A constructor for method initialization only. Later,
   * use {@link #getLocalVariable(BCMethod, AttributeReader)}
   * intead.
   *
   * @param meth - initializing method,
   * @param id - number (index) of this local variable
   *     in method <code>m</code>,
   * @param aname - name of this variable,
   * @param lvg - BCEL's representation of this variable.
   */
  public LocalVariable(final BCMethod meth, final int id,
                       final String aname, final LocalVariableGen lvg) {
    super(Code.LOCAL_VARIABLE);
    this.m = meth;
    this.lvar_id = id;
    this.name = aname;
    this.bcelLvGen = lvg;
    this.type = JavaType.getJavaType(lvg.getType().getSignature());
    //    this.type = JavaType1.convert(lvg.getType());
  }

  /**
   * A 'constructor' from AttributeReader.
   *
   * @param m - method in with variable has been declared,
   * @param ar - input stream to load from,
   * @return local variable of index read from
   *     <code>ar</code>,
   * @throws ReadAttributeException - if read index
   *     is greater or equal local variable count
   *     of method <code>m</code>.
   */
  public static LocalVariable getLocalVariable(final BCMethod m,
                                               final AttributeReader ar)
    throws ReadAttributeException {
    final int index = ar.readShort();
    if (index  <  0 || index  > m.getLocalVariableCount()) {
      throw new ReadAttributeException("invalid local variable index: " +
                                       index);
    }
    return m.getLocalVariable(index);
  }

  @Override
  protected JavaType checkType1() {
    return this.type;
  }

  /**
   * @return BCEL's representation of this variable.
   */
  public LocalVariableGen getBcelLvGen() {
    return this.bcelLvGen;
  }

  /**
   * @return method in with this variable has been declared.
   */
  public BCMethod getMethod() {
    return this.m;
  }

  /**
   * @return variable's name.
   */
  public String getName() {
    return this.name;
  }

  @Override
  public JavaType getType1() {
    return this.type;
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    if (this.name != null) {
      return this.name;
    } else {
      return lv();
    }
  }

  /**
   *
   * @return String "lv[i]" representing the local variable.
   */
  private String lv() {
    return "lv[" + this.lvar_id + "]";
  }

  @Override
  public String toString() {
    if (this.name != null) {
      return "lv[" + this.lvar_id + "/" + this.name + "]";
    } else {
      return lv();
    }
  }

  @Override
  public void write(final AttributeWriter aw) {
    aw.writeByte(Code.LOCAL_VARIABLE);
    aw.writeShort(this.lvar_id);
  }

  public int getIndex() {
    return lvar_id;
  }
}
