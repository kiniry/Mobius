package annot.bcexpression;

import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantUtf8;

import annot.bcclass.BCConstantPool;
import annot.bcexpression.javatype.JavaType;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.Code;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;

/**
 * This class represents field reference occurrence.
 * One <code>FieldRef</code> per one field reference
 * occurence.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class FieldRef extends BCExpression {

  /**
   * Index of FieldRef constant in constant pool.
   * It's assumed that it won't change.
   */
  private int cpIndex;

  /**
   * The name of the field.
   */
  private String name;

  /**
   * The type of the field.
   */
  private JavaType type;

  /**
   * A constructor from AttributeReader.
   *
   * @param ar - input stream to load from,
   * @param root - type of expression (last byte read
   *     from <code>ar</code>).
   * @throws ReadAttributeException - if remaining stream
   *     in <code>ar</code> doesn't represent proper
   *     position in constant pool.
   */
  public FieldRef(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    super(ar, root);
  }

  /**
   * A standard constructor.
   *
   * @param cp - Constant pool containing BCEL's
   *     <code>ConstantFieldRef</code> constant.
   *     FieldRef must be related with index
   *     in primary constant pool.
   * @param acpIndex - index in <code>cp</code> where
   *     BCEL's <code>ConstantFieldRef</code> constant
   *     is beeing held.
   */
  public FieldRef(final BCConstantPool cp,
                  final int acpIndex) {
    super(Code.FIELD_REF);
    loadName(cp, acpIndex);
  }


  /**
   * A 'getInstance' method; searches for proper BCEL's
   * <code>ConstantFieldRef</code> constant in given
   * constant pool.
   *
   * @param cp - constant pool to search in,
   * @param name - name of the constant to be searched for.
   * @return A new <code>FieldRef</code> insatnce,
   *     with name equal to the given one, or <b>null</b>
   *     in no proper constant could be found
   *     in <code>cp</code>.
   */
  public static FieldRef getFieldOfName(final BCConstantPool cp,
                                        final String name) {
    for (int i = 0; i  <  cp.getSize(); i++) {
      if (cp.getConstant(i) == null) {
        continue;
      }
      if (!(cp.getConstant(i) instanceof ConstantFieldref)) {
        continue;
      }
      final ConstantFieldref cfr = (ConstantFieldref) cp.getConstant(i);
      final ConstantNameAndType cnt = (ConstantNameAndType) cp.getConstant(cfr
          .getNameAndTypeIndex());
      final ConstantUtf8 cu8 = (ConstantUtf8) cp
          .getConstant(cnt.getNameIndex());
      final String cname = cu8.getBytes();
      if (cname.equals(name)) {
        return new FieldRef(cp, i);
      }
    }
    return null;
  }

  @Override
  protected JavaType checkType1() {
    return this.type;
  }

  @Override
  public JavaType getType1() {
    return this.type;
  }

  /**
   * Loads name and type from constant pool.
   *
   * @param cp - constant pool to load from,
   * @param acpIndex - index of BCEL's
   *     <code>ConstantFieldRef</code> constant,
   *     representing this field.
   */
  private void loadName(final BCConstantPool cp, final int acpIndex) {
    this.cpIndex = acpIndex;
    final ConstantFieldref cfr = (ConstantFieldref) cp.getConstant(cpIndex);
    final ConstantNameAndType cnt = (ConstantNameAndType) cp.getConstant(cfr
        .getNameAndTypeIndex());
    final ConstantUtf8 cu8 = (ConstantUtf8) cp.getConstant(cnt.getNameIndex());
    this.name = cu8.getBytes();
    final ConstantUtf8 signature = (ConstantUtf8) cp.getConstant(cnt
        .getSignatureIndex());
    this.type = JavaType.getJavaType(signature.getBytes());
  }

  @Override
  protected String printCode1(final BMLConfig conf) {
    return this.name;
  }

  @Override
  protected void read(final AttributeReader ar, final int root)
    throws ReadAttributeException {
    final int acpIndex = ar.readShort();
    try {
      loadName(ar.getConstantPool(), acpIndex);
    } catch (final ClassCastException e) {
      throw new ReadAttributeException("invalid position in constant pool: "  +
                                       acpIndex);
    } catch (final NullPointerException n) {
      throw new ReadAttributeException("invalid position in constant pool: " +
                                       acpIndex);
    }
  }
  /**
   * Prints expression as a string. This method should not
   * be called in attributes nor subclasses to get full
   * string representation. Use printLine(conf)
   * in attributes and printCode1(conf) in subclasses.
   *
   * @param conf - see {@link BMLConfig}.
   * @return string representation of expression,
   *     without line-breaking.
   */
  public String printCode(final BMLConfig conf) {
    if (conf.isGoControlPrint()) {
      return controlPrint(conf);
    } else {
      return printCode1(conf);
    }
  }
  @Override
  public String toString() {
    return this.type + " " + this.name;
  }

  @Override
  public void write(final AttributeWriter aw) {
    aw.writeByte(getConnector());
    aw.writeShort(this.cpIndex);
  }

  public String getName() {
    return name;
  }
}
