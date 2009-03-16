/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
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
 * is stored as a class attribute in .class file.
 * Constants stored here are ordinary, BCEL's Constants.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BCConstantPool extends BCCConstantPrinting {

  /**
   * Constant array.
   */
  private Vector < Constant >  constants;

  /**
   * Number of constants in first constant pool.
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
   * then from the second constant pool attribute.
   *
   * @param ajc - JavaClass to initialize from.
   * @throws ReadAttributeException - if second constant
   *     pool attribute format is invalid.
   */
  public BCConstantPool(final JavaClass ajc) throws ReadAttributeException {
    this.jc = ajc;
    this.constants = new Vector < Constant > ();
    final ConstantPoolGen cpg = new ConstantPoolGen(ajc.getConstantPool());
    addStandardConstants(cpg);
    ajc.setConstantPool(cpg.getFinalConstantPool());
    final ConstantPool cp = ajc.getConstantPool();
    this.initialSize = cp.getLength();
    readInCP(cp);
    readInSecondCP(ajc);
  }

  /**
   * Reads in to the internal constant pool representation the content of the
   * first constant pool.
   *
   * @param cp the BCEL representation of the constant pool to read in
   */
  private void readInCP(final ConstantPool cp) {
    for (int i = 0; i  <  this.initialSize; i++) {
      this.constants.add(cp.getConstant(i));
    }
  }

  /**
   * Reads in to the BMLLib constant pool representation the content of the
   * second constant pool. It finds the appropriate attribute and in case
   * it is not empty reads in its contents.
   *
   * @param ajc the BCEL representation of the class to read second constant
   *   pool for
   * @throws ReadAttributeException if the data in the constant pool
   *   representation is invalid
   */
  private void readInSecondCP(final JavaClass ajc)
    throws ReadAttributeException {
    final Attribute[] attrs = ajc.getAttributes();
    final byte[] bytes = findSecondCPAttribute(attrs);
    if (bytes != null) {
      readInSecondCPContent(bytes);
    }
  }

  /**
   * Retrieves the content of the attribute which contains the second constant
   * pool. It examines one by one all the attributes in the given array.
   * The content of the first attribute the name of which corresponds to
   * the name of the second constant pool is returned. In case there is no
   * second constant pool attribute <code>null</code> is returned.
   *
   * @param attrs the array of attributes to retrieve the second constant pool
   *   from
   * @return the content of the second constant pool, or <code>null</code> in
   *   case there is no second constant pool
   */
  private byte[] findSecondCPAttribute(final Attribute[] attrs) {
    byte[] bytes = null;
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        final Unknown ua = (Unknown) attrs[i];
        if (DisplayStyle.SECOND_CONSTANT_POOL_ATTR.equals(ua.getName())) {
          bytes = ua.getBytes();
        }
      }
    }
    return bytes;
  }

  /**
   * Reads in the contents of the second constant pool and remembers its
   * constant in the local representation.
   *
   * @param bytes the content (second_cp field of the structure) of the second
   *   constant pool attribute
   * @throws ReadAttributeException if the data in the constant pool
   *   representation is invalid
   */
  private void readInSecondCPContent(final byte[] bytes)
    throws ReadAttributeException {
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
    cpg.addUtf8(DisplayStyle.ASSERT_TABLE_ATTR);
    cpg.addUtf8(DisplayStyle.INVARIANTS_ATTR);
    cpg.addUtf8(DisplayStyle.METHOD_SPECIFICATION_ATTR);
    cpg.addUtf8(DisplayStyle.SECOND_CONSTANT_POOL_ATTR);
    cpg.addUtf8(DisplayStyle.LOOP_SPECIFICATION_TABLE_ATTR);
    cpg.addUtf8(DisplayStyle.FIELD_MODIFIERS_ATTR);
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
   * second constant pool have indexes starting with
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
   * Prints both constant pools. The grammar to pring out is:
   *    constant-pools ::= constant-pool [ second-constant-pool ] nl
   * where
   *    constant-pool ::= Constant pool: nl constant-pool-content
   *    second-constant-pool ::= Second constant pool: nl constant-pool-content
   *
   * @param a_code the {@link StringBuffer} to append the constant pools to
   * @return Constant pools representation in a StringBuffer
   */
  public StringBuffer printCode(final StringBuffer a_code) {
    a_code.append(DisplayStyle.CONSTANT_POOL_KWD + "\n");
    for (int i = 0; i  <  this.initialSize; i++) {
      a_code.append(printElement(i));
    }
    final int n = this.constants.size();
    if (n == this.initialSize) {
      return a_code;
    }
    a_code.append("\n" + DisplayStyle.SECOND_CONSTANT_POOL_KWD + "\n");
    for (int i = this.initialSize; i  <  n; i++) {
      a_code.append(printElement(i));
    }
    return a_code;
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
    readInCP(cp);
  }

  /**
   * Saves both constant pools to given JavaClass
   * (primary as an ordinary constant pool and secondary
   * as an "second constant pool" class attribute).
   *
   * @param ajc - JavaClass to save to.
   */
  public void save(final JavaClass ajc) {
    final int n = this.constants.size();
    final Constant[] carr = new Constant[this.initialSize];
    for (int i = 0; i  <  this.initialSize; i++) {
      carr[i] = this.constants.elementAt(i);
    }
    ajc.getConstantPool().setConstantPool(carr);
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
    final ConstantPool cp = ajc.getConstantPool();
    final int nameIndex = findConstant(DisplayStyle.SECOND_CONSTANT_POOL_ATTR);
    final int length = file.size();
    final byte[] bytes = baos.toByteArray();
    final Unknown scp = new Unknown(nameIndex, length, bytes, cp);
    final Attribute[] atab = BCClass.addAttribute(ajc.getAttributes(), scp);
    ajc.setAttributes(atab);
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

  /**
   * Returns <code>true</code> only if the index is an index to a second
   * constant pool constant.
   *
   * @param i the index to check
   * @return <code>true</code> when the index is to the second constant pool,
   *   <code>false</code> when the index is to the original constant pool
   */
  public boolean isSecondConstantPoolIndex(final int i) {
    return (i >= initialSize);
  }

}
