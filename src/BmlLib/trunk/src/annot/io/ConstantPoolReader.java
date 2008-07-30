package annot.io;

import java.io.DataInputStream;
import java.io.IOException;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Constant;
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
   * @param file - input stream containing constant pool in
   *     BCEL format.
   * @return - read constant.
   * @throws ReadAttributeException - if <code>file</code>
   *     input stream data is invalid.
   */
  public static Constant readConstant(final DataInputStream file)
    throws ReadAttributeException {
    try {
      final byte b = file.readByte();
      switch (b) {
        case Constants.CONSTANT_Utf8:
          return new ConstantUtf8(file.readUTF());
        default:
          throw new ReadAttributeException("Unknown constant: " + b);
      }
    } catch (final IOException e) {
      throw new ReadAttributeException(
        "Error while reading second constant pool");
    }
  }
}
