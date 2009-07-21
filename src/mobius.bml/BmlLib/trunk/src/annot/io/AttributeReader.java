package annot.io;

import java.util.Vector;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Unknown;

import annot.attributes.AttributeNames;
import annot.attributes.IBCAttribute;
import annot.attributes.field.BMLModifierAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCConstantPool;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcclass.MessageLog;
import annot.bcexpression.ArithmeticExpression;
import annot.bcexpression.ArrayAccess;
import annot.bcexpression.ArrayLength;
import annot.bcexpression.BCExpression;
import annot.bcexpression.BooleanExpression;
import annot.bcexpression.BoundVar;
import annot.bcexpression.ConditionalExpression;
import annot.bcexpression.FieldAccess;
import annot.bcexpression.FieldRef;
import annot.bcexpression.LocalVariable;
import annot.bcexpression.NULL;
import annot.bcexpression.NumberLiteral;
import annot.bcexpression.OLD;
import annot.bcexpression.RESULT;
import annot.bcexpression.SingleOccurence;
import annot.bcexpression.THIS;
import annot.bcexpression.UnaryArithmeticExpression;
import annot.bcexpression.formula.AbstractFormula;
import annot.bcexpression.formula.Formula;
import annot.bcexpression.formula.Predicate0Ar;
import annot.bcexpression.formula.Predicate2Ar;
import annot.bcexpression.formula.QuantifiedFormula;
import annot.bcexpression.javatype.JavaBasicType;
import annot.bcexpression.javatype.JavaType;
import annot.bcexpression.modifies.ModifiesArray;
import annot.bcexpression.modifies.ModifiesDot;
import annot.bcexpression.modifies.ModifiesIdent;
import annot.bcexpression.modifies.ModifiesInterval;
import annot.bcexpression.modifies.ModifiesLocalVar;
import annot.bcexpression.modifies.ModifiesSingleIndex;
import annot.bcexpression.modifies.ModifiesStar;
import annot.bcexpression.modifies.ModifyExpression;
import annot.bcexpression.modifies.SpecArray;
import bmllib.utils.NumberUtils;

/**
 * This class is responsible for loading BML attributes from
 * BCEL's Unknown atribute. It should be created for a BCClass
 * or BCMethod, BML attribute can be loaded using
 * {@link #readAttribute(Unknown)} method.
 * This class contains data 'stream' (as a byte array) and
 * environment needed to read an expression (eg. bound
 * variables table).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class AttributeReader {

  /**
   * Current attribute's name, used for displaying error
   * message only.
   */
  private String attrName = "?"; // debug

  /**
   * Class containing currently read attributes.
   */
  private final BCClass bcc;

  /**
   * Bound variables table. Contains declared (currently
   * visible) bound variables, with right-most, most
   * recently declared at the end.
   */
  private final Vector < BoundVar >  bvars;

  /**
   * Input stream (from BCEL's Unknown attribute).
   */
  private byte[] input;

  /**
   * Initial length of input stream (after finished reading
   * of attribute, <code>pos</code> should be equal to
   * <code>length</code>.
   */
  private int length;

  /**
   * Method containing currently read attribute, if any.
   */
  private BCMethod method;

  /**
   * Field containing currently read attribute, if any.
   */
  private BMLModifierAttribute modifier;

  // environment:

  /**
   * Current position in input stream.
   */
  private int pos;

  /**
   * An array with objects into which the content of different
   * BML attributes should currently be read in.
   */
  private IBCAttribute[] attributeHandlers =
    new IBCAttribute[AttributeNames.BML_ATTRIBUTE_NAMES.length];

  /**
   * A Constructor used for reading class attributes.
   *
   * @param classRepresentation - class that read attributes should be
   * attached to.
   */
  public AttributeReader(final BCClass classRepresentation) {
    this.bcc = classRepresentation;
    this.bvars = new Vector < BoundVar > ();
    this.attributeHandlers[AttributeNames.SECOND_CONSTANT_POOL_ATTR_POS] =
      this.bcc.getCp();
    this.attributeHandlers[AttributeNames.INVARIANTS_ATTR_POS] =
      this.bcc.getInvariantTable();
    this.attributeHandlers[AttributeNames.GHOST_FIELDS_ATTR_POS] =
      this.bcc.getGhostFields();
  }

  /**
   * A Constructor used for reading method attributes.
   *
   * @param bcm - method that read attributes should be
   * attached to.
   */
  public AttributeReader(final BCMethod bcm) {
    this.bcc = bcm.getBcc();
    this.method = bcm;
    this.bvars = new Vector < BoundVar > ();
    this.attributeHandlers[AttributeNames.METHOD_SPECIFICATION_ATTR_POS] =
      method.getMspec();
    this.attributeHandlers[AttributeNames.ASSERT_TABLE_ATTR_POS] =
      this.method.getAmap().getAtab();
    this.attributeHandlers[AttributeNames.LOOP_SPECIFICATION_TABLE_ATTR_POS] =
      this.method.getAmap().getLstab();
  }

  /**
   *
   * @param amodifier
   */
  public AttributeReader(final BMLModifierAttribute amodifier) {
    this.bcc = null;
    this.modifier = amodifier;
    this.bvars = new Vector < BoundVar > ();
    this.attributeHandlers[AttributeNames.FIELD_MODIFIERS_ATTR_POS] =
      this.modifier;
  }

  /**
   * Checks that there is enough data left in the
   * <code>input</code> stream.
   *
   * @param n - number of bytes needed to be avaliable.
   * @throws ReadAttributeException - if there is less than
   *     <code>n</code> bytes left in the stream.
   */
  private void chkRange(final int n) throws ReadAttributeException {
    if (this.pos + n  >  this.length) {
      throw new ReadAttributeException("end of input stream in " +
                                       this.attrName + " (size=" +
                                       this.length + ")");
    }
  }

  /**
   * Gives String value of constant with given index, from
   * constant pool.
   *
   * @param index - index of searched constant.
   * @return String value of Utf8 constant (from constant
   *     pool) of given index.
   * @throws ReadAttributeException - if there are no Utf8
   *     constant at given index in constant pool.
   */
  public String findString(final int index) throws ReadAttributeException {
    final Constant c = this.bcc.getCp().getConstant(index);
    if (c instanceof ConstantUtf8) {
      return ((ConstantUtf8) c).getBytes();
    }
    throw new ReadAttributeException("invalid constant index: " + index);
  }

  /**
   * @param index - variable index.
   * @return Visible bound variable of given index.
   * @see #bvars
   */
  public BoundVar getBvar(final int index) {
    return this.bvars.elementAt(index);
  }

  /**
   * @return Number of currently visible bound variables.
   */
  public int getBvarCount() {
    return this.bvars.size();
  }

  /**
   * @return Currently visible bound variable Vector.
   */
  public Vector < BoundVar >  getBvars() {
    return this.bvars;
  }

  /**
   * Return the BML constant pool associated with the currently processed
   * class.
   *
   * @return the constant pool
   */
  public BCConstantPool getConstantPool() {
    return this.bcc.getCp();
  }

  /**
   * Creates proper BML attribute (IBCAttribute, not exactly
   * BCPrintableAttribute) depending on given Unknown
   * attribute's name, loads it from given Unknown attribute
   * and attach to BCClass or BCMethod given in the
   * constructor.
   *
   * @param ua - (BCEL) Unknown attribute to load from.
   * @throws ReadAttributeException - if the structure of the attribute
   *   is not correct
   */
  public void readAttribute(final Unknown ua) throws ReadAttributeException {
    final String aname = ua.getName();
    this.attrName = ua.getName();
    this.input = ua.getBytes();
    this.length = ua.getLength();
    this.pos = 0;
    for (int i = 0; i < AttributeNames.BML_ATTRIBUTE_NAMES.length; i++) {
      if (attrName.equals(AttributeNames.BML_ATTRIBUTE_NAMES[i])) {
        if (attributeHandlers[i] != null) {
          MLog.putMsg(MessageLog.LEVEL_PINFO, "    reading attribute: " +
                      AttributeNames.BML_ATTRIBUTE_NAMES[i]);
          attributeHandlers[i].load(this);
          return;
        } else {
          MLog.putMsg(MessageLog.LEVEL_PTODO,
                      "    unexpected attribute: " + aname);
        }
      }
    }
    MLog.putMsg(MessageLog.LEVEL_PTODO,
                "    unrecognized attribute: " + aname);
    if (this.pos != this.length) {
      throw new ReadAttributeException(this.length - this.pos + " of " +
                                       this.length + " bytes unread!");
    }
  }

  /**
   * Reads the count (2 bytes integer) of particular kind of items from
   * <code>input</code> stream.
   *
   * @return the count of items to be read
   * @throws ReadAttributeException - if there is not enough
   *   bytes in the stream to read the item count
   */
  public int readItemsCount() throws ReadAttributeException {
    return readShort();
  }

  /**
   * Reads a byte from the representation of the
   * currently processed attribute.
   *
   * @return read byte.
   * @throws ReadAttributeException - if there is not enough
   *     bytes in the stream to read a byte.
   */
  public int readByte() throws ReadAttributeException {
    chkRange(1);
    final int b = this.input[this.pos] & NumberUtils.LOWEST_BYTE_MASK;
    this.pos++;
    return b;
  }


  /**
   * Reads a given number of bytes from the representation of the
   * currently processed attribute.
   *
   * @param len the number of bytes to read
   * @return the bytes which were read
   * @throws ReadAttributeException - if there is not enough
   *     bytes in the stream to read the array
   */
  public byte[] readBytes(final int len)
    throws ReadAttributeException {
    chkRange(len);
    final byte[] res = new byte[len];
    System.arraycopy(input, pos, res, 0, len);
    this.pos += len;
    return res;
  }

  /**
   * Reads an expression from <code>input</code> stream.
   *
   * @return Read expression.
   * @throws ReadAttributeException - if data in the stream
   *     doesn't represent correct expression.
   */
  public BCExpression readExpression() throws ReadAttributeException {
    final int b = readByte();
    switch (b) {
      case Code.TRUE:
      case Code.FALSE:
        return new Predicate0Ar(b);
      case Code.AND:
      case Code.OR:
      case Code.IMPLIES:
      case Code.NOT:
      case Code.EQUIV:
      case Code.NOTEQUIV:
        return new Formula(this, b);
      case Code.LESS:
      case Code.LESSEQ:
      case Code.EQ:
      case Code.NOTEQ:
      case Code.GRT:
      case Code.GRTEQ:
        return new Predicate2Ar(this, b);
      case Code.PLUS:
      case Code.MINUS:
      case Code.MULT:
      case Code.DIV:
      case Code.REM:
      case Code.BITWISEAND:
      case Code.BITWISEOR:
      case Code.BITWISEXOR:
      case Code.SHL:
      case Code.SHR:
      case Code.USHR:
        return new ArithmeticExpression(this, b);
      case Code.NEG:
      case Code.BITWISENOT:
        return new UnaryArithmeticExpression(this, b);
      case Code.INT_LITERAL:
        return new NumberLiteral(this, b);
      case Code.COND_EXPR:
        return new ConditionalExpression(this, b);
      case Code.NULL:
        return new NULL();
      case Code.THIS:
        return new THIS(this.bcc);
      case Code.RESULT:
        return new RESULT(this.method);
      case Code.ARRAYLENGTH:
        return new ArrayLength(this, b);
      case Code.LOCAL_VARIABLE:
        return new SingleOccurence(LocalVariable.getLocalVariable(this.method,
                                                                  this));
      case Code.FIELD_REF:
        return new FieldRef(this, b);
      case Code.ARRAY_ACCESS:
        return new ArrayAccess(this, b);
      case Code.FIELD_ACCESS:
        return new FieldAccess(this, b);
      case Code.OLD:
        return new OLD(this, b);
      case Code.FORALL:
      case Code.EXISTS:
      case Code.FORALL_WITH_NAME:
      case Code.EXISTS_WITH_NAME:
        return new QuantifiedFormula(this, b);
      case Code.BOUND_VAR:
        return new SingleOccurence(BoundVar.getBoundVar(this));
      case Code.JAVA_TYPE:
        final int i = readShort();
        final Constant c = this.bcc.getCp().getConstant(i);
        if (!(c instanceof ConstantUtf8)) {
          throw new ReadAttributeException("Utf8 expected as javaType name");
        }
        final String name = ((ConstantUtf8) c).getBytes();
        return JavaType.getJavaType(name);
      default:
        throw new ReadAttributeException("Unknown expression code: " + b);
    }
  }

  /**
   * Reads an Expression and checks that it is a formula.
   *
   * @return Read expression.
   * @throws ReadAttributeException - if data in the stream
   *     doesn't represent correct formula.
   */
  public AbstractFormula readFormula() throws ReadAttributeException {
    final BCExpression expr = readExpression();
    if (expr instanceof AbstractFormula) {
      final AbstractFormula af = (AbstractFormula) expr;
      return af;
    }
    if (expr.checkType() == JavaBasicType.JavaBool) {
      return new BooleanExpression(expr);
    }
    throw new ReadAttributeException("Formula expected");
  }

  /**
   * Reads an integer (4 bytes) from  the representation of the
   * currently processed attribute.
   *
   * @return read int.
   * @throws ReadAttributeException - if there is not enough
   *     bytes in the stream to read an int.
   */
  public int readInt() throws ReadAttributeException {
    chkRange(NumberUtils.INTEGER_IN_BYTES);
    int i = (this.input[this.pos] & NumberUtils.LOWEST_BYTE_MASK)  <<
      NumberUtils.THREE_BYTES_SIZE;
    i += (this.input[this.pos + NumberUtils.FIRST_BYTE] &
        NumberUtils.LOWEST_BYTE_MASK)  << NumberUtils.TWO_BYTES_SIZE;
    i += (this.input[this.pos + NumberUtils.SECOND_BYTE] &
        NumberUtils.LOWEST_BYTE_MASK)  << NumberUtils.ONE_BYTE_SIZE;
    i += this.input[this.pos + NumberUtils.THIRD_BYTE] &
        NumberUtils.LOWEST_BYTE_MASK;
    this.pos += NumberUtils.INTEGER_IN_BYTES;
    return i;
  }


  /**
   * Reads a long (8 bytes) from  the representation of the
   * currently processed attribute.
   *
   * @return read int.
   * @throws ReadAttributeException - if there is not enough
   *     bytes in the stream to read an int.
   */
  public long readLong() throws ReadAttributeException {
    final int high_bytes = readInt();
    final int low_bytes = readInt();
    long res = high_bytes;
    res = (res << Integer.SIZE) | low_bytes;
    return res;
  }
  /**
   * Returns proper instance of ModifyExpression. Use this
   * instead of creating new instances yourself.
   *
   * @return proper instance of ModifyExpression.
   * @throws ReadAttributeException - if remaining data
   *     doesn't represent correct modify expression.
   */
  public ModifyExpression readModifyExpression() throws ReadAttributeException {
    final int b = readByte();
    ModifyExpression res;
    switch (b) {
      case Code.MODIFIES_NOTHING:
        res = ModifyExpression.NOTHING_MODIF;
        break;
      case Code.MODIFIES_EVERYTHING:
        res = ModifyExpression.EVERYTHING_MODIF;
        break;
      case Code.MODIFIES_IDENT:
        res = new ModifiesIdent(this, b);
        break;
      case Code.MODIFIES_DOT:
        res = new ModifiesDot(this, b);
        break;
      case Code.MODIFIES_ARRAY:
        res = new ModifiesArray(this, b);
        break;
      case Code.MODIFIES_LOCAL_VARIABLE:
        res = new ModifiesLocalVar(this, b);
        break;
      default:
        throw new ReadAttributeException("invalid modify opcode: " + b);
    }
    return res;
  }

  /**
   * Reads an short integer (2 bytes) from the representation of the
   * currently processed attribute.
   *
   * @return read int.
   * @throws ReadAttributeException - if there is not enough
   *     bytes in the stream to read a short integer.
   */
  public int readShort() throws ReadAttributeException {
    chkRange(NumberUtils.SHORT_IN_BYTES);
    final int s =
      ((this.input[this.pos] & NumberUtils.LOWEST_BYTE_MASK)  <<
          NumberUtils.ONE_BYTE_SIZE) +
      (this.input[this.pos + 1] & NumberUtils.LOWEST_BYTE_MASK);
    this.pos += NumberUtils.SHORT_IN_BYTES;
    return s;
  }

  /**
   * Returns proper instance of SpecArray (specification of
   * which elements of an array can be modified). Use this
   * instead of creating new instances yourself.
   *
   * @return proper instance of SpecArray.
   * @throws ReadAttributeException - if remaining data
   *     doesn't represent correct specArray.
   */
  public SpecArray readSpecArray() throws ReadAttributeException {
    final int b = readByte();
    switch (b) {
      case Code.MODIFIES_STAR:
        return new ModifiesStar();
      case Code.MODIFIES_SINGLE_INDEX:
        return new ModifiesSingleIndex(this, b);
      case Code.MODIFIES_INTERVAL:
        return new ModifiesInterval(this, b);
      default:
        throw new ReadAttributeException("invalid specArray opcode: " + b);
    }
  }

  /**
   * This method returns the length of the currently processed
   * attribute.
   *
   * @return the length of the current attribute
   */
  public int getLength() {
    return length;
  }

  /**
   * Returns the byte representation of the currently processed
   * attribute.
   *
   * @return the byte representation of the currently processed attribute.
   */
  public byte[] getInput() {
    return input;
  }


}
