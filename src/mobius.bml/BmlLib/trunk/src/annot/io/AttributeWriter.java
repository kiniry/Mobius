package annot.io;

import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.Unknown;

import bmllib.utils.NumberUtils;

import annot.attributes.IBCAttribute;
import annot.bcclass.BCClassRepresentation;
import annot.bcclass.BCConstantPool;
import annot.bcclass.BCMethod;
import annot.bcclass.MLog;
import annot.bcclass.MessageLog;

/**
 * This class is used to write BML attributes (of IBCAttribute
 * type) to the BCEL's Unkonwn attribute.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class AttributeWriter {

  /**
   * The binary buffer with attribute content is increased by this factor.
   */
  private static final int BUFFER_INCREASE_FACTOR = 2;

  /**
   * BCClass containing attributes to be written.
   */
  private final BCClassRepresentation bcc;

  /**
   * BCMethod containing attributes to be written.
   */
  private BCMethod bcm;

  /**
   * Output 'stream' to write attributes to.
   * XXX should be replaced with Vector < byte > .
   */
  private byte[] output;

  /**
   * Position in the output stream.
   */
  private int pos;

  /**
   * A contructor for BCClass (to write class atributes).
   *
   * @param classRepresentation - class containing attributes to be written.
   */
  public AttributeWriter(final BCClassRepresentation classRepresentation) {
    this.bcc = classRepresentation;
  }

  /**
   * A constructor for BCMethod (to write method attriutes).
   *
   * @param abcm - method containing attributes to be written.
   */
  public AttributeWriter(final BCMethod abcm) {
    this.bcc = abcm.getBcc();
    this.bcm = abcm;
  }

  /**
   * Searches for Utf8 constant in constant pool constaining
   * given String, returning it's index. If it cannot
   * be found, a new UtfConstant is created and appended
   * to the second constant pool (and it's index
   * is returned).
   *
   * @param str - String to search for.
   * @return Index of Utf8 constant with given String.
   */
  public int findConstant(final String str) {
    final int constPos = this.bcc.getCp().findConstant(str);
    if (constPos == -1) {
      final ConstantUtf8 cu8 = new ConstantUtf8(str);
      this.bcc.getCp().addConstant(cu8, true, null);
      return this.bcc.getCp().getSize() - 1;
    }
    return constPos;
  }

  /**
   * @return current method.
   */
  public BCMethod getBcm() {
    return this.bcm;
  }

  /**
   * Increases stream capacity twice, if nessesery.
   *
   * @param n - number of bytes that needs to be avaliable
   *     to write int the stream.
   */
  private void grow(final int n) {
    if (this.pos + n  >  this.output.length) {
      final byte[] arr = new byte[this.output.length * BUFFER_INCREASE_FACTOR];
      for (int i = 0; i  <  this.output.length; i++) {
        arr[i] = this.output[i];
      }
      this.output = arr;
    }
  }

  /**
   * Writes given attribute (of IBCAttribute interface),
   * creating BCEL's Unknown attribute. It makes sure the attribute
   * name is in the constant pool of the class to be written.
   *
   * @param attr - Attribute to be written,
   * @return Uknonwn attribute representing given attribute.
   */
  public Unknown writeAttribute(final IBCAttribute attr) {
    MLog.putMsg(MessageLog.LEVEL_PINFO,
                "    writing attribute: " + attr.getName());
    this.output = new byte[NumberUtils.INTEGER_IN_BYTES];
    this.pos = 0;
    attr.save(this);
    final byte[] bytes = new byte[this.pos];
    final BCConstantPool bcp = bcc.getCp();
    int where = bcp.findConstant(attr.getName());
    final Constant constnt = new ConstantUtf8(attr.getName());
    if (where < 0) {
      bcp.addConstant(constnt, false, null);
      where = bcp.findConstant(attr.getName());
    }
    if (bcp.isSecondConstantPoolIndex(where)) {
      bcp.addConstant(constnt, false, null);
    }
    System.arraycopy(output, 0, bytes, 0, this.pos);
    return new Unknown(attr.getIndex(), this.pos, bytes,
      this.bcc.getBCELClass().getConstantPool().getFinalConstantPool());
  }

  /**
   * Writes a attribute count (2 bytes) to the stream.
   *
   * @param s - attribute count to be written.
   */
  public void writeAttributeCount(final int s) {
    writeShort(s);
  }

  /**
   * Writes a byte to the stream.
   *
   * @param b - byte to be written.
   */
  public void writeByte(final int b) {
    grow(NumberUtils.BYTE_IN_BYTES);
    this.output[this.pos] = (byte) (b & NumberUtils.LOWEST_BYTE_MASK);
    this.pos++;
  }

  /**
   * Writes an integer (4 bytes) to the stream.
   *
   * @param i - integer to be written.
   */
  public void writeInt(final int i) {
    grow(NumberUtils.INTEGER_IN_BYTES);
    this.output[this.pos] =
      (byte) (i  >>  NumberUtils.THREE_BYTES_SIZE &
              NumberUtils.LOWEST_BYTE_MASK);
    this.output[this.pos + NumberUtils.FIRST_BYTE] =
      (byte) (i  >>  NumberUtils.TWO_BYTES_SIZE &
              NumberUtils.LOWEST_BYTE_MASK);
    this.output[this.pos + NumberUtils.SECOND_BYTE] =
      (byte) (i  >>  NumberUtils.ONE_BYTE_SIZE &
              NumberUtils.LOWEST_BYTE_MASK);
    this.output[this.pos + NumberUtils.THIRD_BYTE] =
      (byte) (i & NumberUtils.LOWEST_BYTE_MASK);
    this.pos += NumberUtils.INTEGER_IN_BYTES;
  }

  /**
   * Writes an short integer (2 bytes) to the stream.
   *
   * @param s - integer to be written (less than 2^15).
   */
  public void writeShort(final int s) {
    grow(NumberUtils.SHORT_IN_BYTES);
    this.output[this.pos] = (byte) (s  >>  NumberUtils.ONE_BYTE_SIZE &
        NumberUtils.LOWEST_BYTE_MASK);
    this.output[this.pos + 1] = (byte) (s & NumberUtils.LOWEST_BYTE_MASK);
    this.pos += NumberUtils.SHORT_IN_BYTES;
  }

  /**
   * Writes an array of bytes.
   *
   * @param byteArray the bytes to write to
   */
  public void writeBytes(final byte[] byteArray) {
    grow(byteArray.length);
    System.arraycopy(byteArray, 0, output, pos, byteArray.length);
  }

}
