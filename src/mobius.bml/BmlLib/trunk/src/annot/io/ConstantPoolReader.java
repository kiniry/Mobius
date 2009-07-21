package annot.io;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantDouble;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantFloat;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantInterfaceMethodref;
import org.apache.bcel.classfile.ConstantLong;
import org.apache.bcel.classfile.ConstantMethodref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;

/**
 * This class is used to read BCEL's Constants from
 * DataInputStream (in BCEL's format). I couldn't use BCEL
 * to do this, becouse proper constructors and factories
 * are not visible from the outside, so I have to copy
 * nessesery code from BCEL (as the second constant pool
 * format is exactly the same as original constant pool
 * format) in hope that they won't change it.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public final class ConstantPoolReader {

  /**
   * An empty private constructor to disallow the creation of instances.
   */
  private ConstantPoolReader() {
  }

  /**
   * Reads a constant from given stream.
   *
   * @param attributeReader - input stream containing constant pool in
   *     BCEL format.
   * @return - read constant.
   * @throws ReadAttributeException - if <code>file</code>
   *     input stream data is invalid.
   */
  public static Constant readConstant(final AttributeReader attributeReader)
    throws ReadAttributeException {
    final int b = attributeReader.readByte();
    switch (b) {
      case Constants.CONSTANT_Utf8:
        final int len = attributeReader.readShort();
        final String bytes =
          new String(attributeReader.readBytes(len));
        return new ConstantUtf8(bytes);
      case Constants.CONSTANT_Integer:
        final int val = attributeReader.readInt();
        return new ConstantInteger(val);
      case Constants.CONSTANT_Float:
        final float fval = Float.intBitsToFloat(attributeReader.readInt());
        return new ConstantFloat(fval);
      case Constants.CONSTANT_Long:
        final long lval = attributeReader.readLong();
        return new ConstantLong(lval);
      case Constants.CONSTANT_Double:
        final double dval = Double.longBitsToDouble(attributeReader.readLong());
        return new ConstantDouble(dval);
      case Constants.CONSTANT_Class:
        final int cidx = attributeReader.readShort();
        return new ConstantClass(cidx);
      case Constants.CONSTANT_Fieldref:
        final int cidx1 = attributeReader.readShort();
        final int nref1 = attributeReader.readShort();
        return new ConstantFieldref(cidx1, nref1);
      case Constants.CONSTANT_String:
        final int sidx = attributeReader.readShort();
        return new ConstantString(sidx);
      case Constants.CONSTANT_Methodref:
        final int cidx2 = attributeReader.readShort();
        final int nref2 = attributeReader.readShort();
        return new ConstantMethodref(cidx2, nref2);
      case Constants.CONSTANT_InterfaceMethodref:
        final int cidx3 = attributeReader.readShort();
        final int nref3 = attributeReader.readShort();
        return new ConstantInterfaceMethodref(cidx3, nref3);
      case Constants.CONSTANT_NameAndType:
        final int nidx = attributeReader.readShort();
        final int tidx = attributeReader.readShort();
        return new ConstantNameAndType(nidx, tidx);
      default:
        throw new ReadAttributeException("Unknown constant: " + b);
    }
  }
}
