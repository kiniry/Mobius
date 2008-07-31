package annot.bcclass;

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.DataInputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ConstantPoolGen;

import annot.io.ConstantPoolReader;
import annot.io.ReadAttributeException;
import annot.textio.DisplayStyle;

/**
 * This class represents extended constant pool, that contains
 * all constants from original (BCEL) constant pool and
 * constants from second constant pool. Second constant pool
 * is stored as an class attribute in .class file.
 * Constants stored here are ordinary, BCEL's Constants.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BCConstantPool {

  /**
   * Constant array.
   */
  private Vector < Constant >  constants;

  /**
   * Number of constants in main (BCEL's) constant pool.
   */
  private int initialSize;

  /**
   * JavaClass related with it's primary constantPool,
   * used for {@link #reset()} method.
   */
  private final JavaClass jc;

  /**
   * A standard constructor, from JavaClass. It inserts
   * constants from ordinary constant pool first, and
   * then from secons constant pool attribute.
   *
   * @param jc - JavaClass to initialize from.
   * @throws ReadAttributeException - if second constant
   *     pool attribute format is invalid.
   */
  public BCConstantPool(final JavaClass jc) throws ReadAttributeException {
    this.jc = jc;
    this.constants = new Vector < Constant > ();
    final ConstantPoolGen cpg = new ConstantPoolGen(jc.getConstantPool());
    addStandardConstants(cpg);
    jc.setConstantPool(cpg.getFinalConstantPool());
    final ConstantPool cp = jc.getConstantPool();
    this.initialSize = cp.getLength();
    for (int i = 0; i  <  this.initialSize; i++) {
      this.constants.add(cp.getConstant(i));
    }
    final Attribute[] attrs = jc.getAttributes();
    byte[] bytes = null;
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        final Unknown ua = (Unknown) attrs[i];
        if (DisplayStyle.__second_cp.equals(ua.getName())) {
          bytes = ua.getBytes();
        }
      }
    }
    if (bytes != null) {
      MLog.putMsg(MessageLog.LEVEL_PNOTICE, "second constant pool detected.");
      final DataInputStream file = new DataInputStream(
        new ByteArrayInputStream(bytes));
      try {
        final int size = file.readUnsignedShort();
        for (int i = 0; i  <  size; i++) {
          final Constant c = ConstantPoolReader.readConstant(file);
          this.constants.add(c);
        }
      } catch (final IOException e) {
        throw new ReadAttributeException("error while reading second " +
                                         "constant pool");
      }
    }
  }

  /**
   * Appends a constant to the second constant pool.
   *
   * @param c - Constant to be added.
   */
  public void addConstant(final Constant c) {
    this.constants.add(c);
  }

  /**
   * Adds standard constants (eg. attribute names) to the
   * primary (BCEL) constant pool. This should be called only
   * between loading primary and secondary constant pool.
   *
   * @param cpg - BCEL's constant pool generator,
   *     from JavaClass.
   */
  private void addStandardConstants(final ConstantPoolGen cpg) {
    cpg.addUtf8(DisplayStyle.JT_INT);
    cpg.addUtf8(DisplayStyle.__assertTable);
    cpg.addUtf8(DisplayStyle.__classInvariant);
    cpg.addUtf8(DisplayStyle.__mspec);
    cpg.addUtf8(DisplayStyle.__second_cp);
    cpg.addUtf8(DisplayStyle.__loopSpecTable);
  }

  /**
   * Searches for an Utf8Constant with data equal to
   * <code>str</code> in both primary and secondary constant
   * pools.
   *
   * @param cdata - string to search for.
   * @return index of matching Constant or -1 if no
   *     Constant could be found.
   */
  public int findConstant(final String cdata) {
    final int n = this.constants.size();
    for (int i = 0; i  <  n; i++) {
      final Constant c = this.constants.elementAt(i);
      if (c instanceof ConstantUtf8) {
        final ConstantUtf8 uc8 = (ConstantUtf8) c;
        if (cdata.equals(uc8.getBytes())) {
          return i;
        }
      }
    }
    return -1;
  }

  /**
   * Gives a constant from constant pool. Constants from
   * second constant pool have indexes starting from
   * <code>initialSize</code>, while constants from primary
   * constant pool have indexes from 0 to initialSize - 1.
   * Can be used in loading from file only.
   *
   * @param i - constant index
   * @return i-th constant.
   */
  public Constant getConstant(final int i) {
    return this.constants.elementAt(i);
  }

  /**
   * Prints both constant pools.
   *
   * @return Constant pools String representation.
   */
  public String printCode() {
    String code = "**** primary constant pool ****\n";
    for (int i = 0; i  <  this.initialSize; i++) {
      code += printElement(i);
    }
    final int n = this.constants.size();
    if (n == this.initialSize) {
      return code;
    }
    code += "*** secondary constant pool ****\n";
    for (int i = this.initialSize; i  <  n; i++) {
      code += printElement(i);
    }
    return code;
  }

  /**
   * Displays i-th constant like:
   *   i :  CONSTANT_Utf8[1]("Code")
   *
   * @param i - constant's index.
   * @return a String like described above.
   */
  private String printElement(final int i) {
    final Constant c = this.constants.elementAt(i);
    if (c == null) {
      return "";
    }
    return (i  <  100 ? " " : "") + (i  <  10 ? " " : "") + i + ": " +
      c.toString() + "\n";
  }

  /**
   * Reinitializes constant pool from it's JavaClass'es
   * primary constant pool, removing all variables from
   * secondary constant pool.
   */
  public void reset() {
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "clearing second constant pool");
    this.constants = new Vector < Constant > ();
    final ConstantPoolGen cpg = new ConstantPoolGen(this.jc.getConstantPool());
    addStandardConstants(cpg);
    this.jc.setConstantPool(cpg.getFinalConstantPool());
    final ConstantPool cp = this.jc.getConstantPool();
    this.initialSize = cp.getLength();
    for (int i = 0; i  <  this.initialSize; i++) {
      this.constants.add(cp.getConstant(i));
    }
  }

  /**
   * Saves both constant pools to given JavaClass
   * (primary as an ordinary constant pool and secondary
   * as an "second constant pool" class attribute).
   *
   * @param jc - JavaClass to save to.
   */
  public void save(final JavaClass jc) {
    final int n = this.constants.size();
    final Constant[] carr = new Constant[this.initialSize];
    for (int i = 0; i  <  this.initialSize; i++) {
      carr[i] = this.constants.elementAt(i);
    }
    jc.getConstantPool().setConstantPool(carr);
    final ByteArrayOutputStream baos = new ByteArrayOutputStream();
    final DataOutputStream file = new DataOutputStream(baos);
    try {
      file.writeShort(n - this.initialSize);
      for (int i = this.initialSize; i  <  n; i++) {
        this.constants.elementAt(i).dump(file);
      }
    } catch (final IOException e) {
      e.printStackTrace();
      throw new RuntimeException("io error in BCConstantPool.save()");
    }
    final ConstantPool cp = jc.getConstantPool();
    final int nameIndex = findConstant(DisplayStyle.__second_cp);
    final int length = file.size();
    final byte[] bytes = baos.toByteArray();
    final Unknown scp = new Unknown(nameIndex, length, bytes, cp);
    final Attribute[] atab = BCClass.addAttribute(jc.getAttributes(), scp);
    jc.setAttributes(atab);
  }

  /**
   * Searches for an Utf8Constant with data equal to
   * <code>str</code> in both primary and secondary constant
   * pools.
   *
   * @param str - string to search for.
   * @return matching Constant or null if no Constant
   *     could be found.
   */
  public Constant searchForString(final String str) {
    final int pos = findConstant(str);
    if (pos == -1) {
      return null;
    }
    return getConstant(pos);
  }

  /**
   * @return number of constants stored in both
   *     constant pools.
   */
  public int size() {
    return this.constants.size();
  }

}
