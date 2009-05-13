/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

import java.io.ByteArrayOutputStream;
import java.io.DataOutputStream;
import java.io.IOException;
import java.util.Vector;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantCP;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ConstantPoolGen;

import annot.attributes.AttributeNames;
import annot.attributes.IBCAttribute;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
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
public class BCConstantPool extends BCCConstantPrinting
                            implements IBCAttribute {

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
   * constants from ordinary constant pool first, but it does
   * not read in the second constant pool. This waits until
   * the class attributes are read.
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
   * Appends a constant to the second constant pool.
   *
   * @param c - Constant to be added.
   * @param toSecondCP - <code>true</code> in case the constant should be
   *   added to the second constant pool, <code>false</code> in case this
   *   should be added to the first one
   */
  public void addConstant(final Constant c,
                          final boolean toSecondCP) {
    if (toSecondCP) {
      this.constants.add(c);
    } else {
      this.constants.add(initialSize++, c);
      final Constant[] consts = new Constant[initialSize];
      for (int i = 0; i < initialSize; i++) {
        consts[i] = constants.get(i);
      }
      jc.getConstantPool().setConstantPool(consts);
    }
  }

  /**
   * Appends a constant to the constant pool after the constant at the given
   * index.
   *
   * @param c - Constant to be added.
   * @param an_index - An index of constant after which the constant should
   * be added.
   * @param toSecondCP - <code>true</code> in case the constant should be
   *   added to the second constant pool, <code>false</code> in case this
   *   should be added to the first one
   */
  public void addConstantAfter(final Constant c, final int an_index,
                               final boolean toSecondCP) {
    final int index = an_index + 1;
    if (toSecondCP) {
      this.constants.add(index, c);
    } else {
      this.constants.add(index, c);
      initialSize++;
      final Constant[] consts = new Constant[initialSize];
      for (int i = 0; i < initialSize; i++) {
        consts[i] = constants.get(i);
      }
      jc.getConstantPool().setConstantPool(consts);
    }
  }
  
  /**
   * Removes all entries from constant pool.
   * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl) 
   */
  public void clearConstantPool() {
    constants.clear();
    initialSize = 0;
    addConstant(null, false);
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
    cpg.addUtf8(AttributeNames.ASSERT_TABLE_ATTR);
    cpg.addUtf8(AttributeNames.INVARIANTS_ATTR);
    cpg.addUtf8(AttributeNames.METHOD_SPECIFICATION_ATTR);
    cpg.addUtf8(AttributeNames.SECOND_CONSTANT_POOL_ATTR);
    cpg.addUtf8(AttributeNames.LOOP_SPECIFICATION_TABLE_ATTR);
    cpg.addUtf8(AttributeNames.FIELD_MODIFIERS_ATTR);
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
   * Searches for a NameAndType constant with two indicies which are equal
   * to the ones given in the arguments.
   *
   * @param idx1 - the first (name) index
   * @param idx2 - the second (type) index
   * @return index of matching Constant or -1 if no
   *     Constant could be found.
   */
  public int findNATConstant(final int idx1, final int idx2) {
    final int n = this.constants.size();
    for (int i = 0; i  <  n; i++) {
      final Constant c = this.constants.elementAt(i);
      if (c instanceof ConstantNameAndType) {
        final ConstantNameAndType cn = (ConstantNameAndType) c;
        if (idx1 == cn.getNameIndex() &&
            idx2 == cn.getSignatureIndex()) {
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
    final int nameIndex =
      findConstant(AttributeNames.SECOND_CONSTANT_POOL_ATTR);
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

  /**
   * Loads all constants from the second constant pool
   * and inserts them to the current constant pool. It assumes that
   * the given attribute reader is at the position ready to read
   * in the number of the constants in the second constant pool i.e.
   * the field second_cp_count from the structure
   * SecondConstantPool_attribute {
   *   u2 attribute_name_index;
   *   u4 attribute_length;
   *   u2 second_cp_count;
   *   cp_info second_cp[second_cp_count];
   * }
   * from section SecondConstantPool Attribute of BML Reference Manual.
   * @param attributeReader - stream to load annotations from.
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent correct
   *     constant pool
   */
  public void load(final AttributeReader attributeReader)
    throws ReadAttributeException {
    final int size = attributeReader.readShort();
    for (int i = 0; i  <  size; i++) {
      final Constant c = ConstantPoolReader.readConstant(attributeReader);
      this.constants.add(c);
    }
  }

  public int getIndex() {
    // TODO Auto-generated method stub
    return 0;
  }

  public String getName() {
    // TODO Auto-generated method stub
    return null;
  }

  /**
   * Returns the number of constants in first constant pool.
   * @return the number of constants in first constant pool
   */
  public int getInitialSize() {
    return initialSize;
  }

  /**
   * Returns the number of all constants.
   * @return the number of all constants
   */
  public int getSize() {
    return constants.size();
  }


  public void save(final AttributeWriter aw) {
    // TODO Auto-generated method stub
  }

  /**
   * Remove the given constant from the constants vector. It takes care of the
   * case when the constant is from the first constant pool.
   *
   * @param apos the number of the constant to remove
   */
  public void removeConstant(final int apos) {
    constants.remove(apos);
    if (apos < initialSize) {
      initialSize--;
      final Constant[] consts = new Constant[initialSize];
      for (int i = 0; i < initialSize; i++) {
        final Constant mconst = constants.get(i);
        consts[i] = mconst;
        if (mconst != null) {
          switch (constants.get(i).getTag()) { //recalculation of indexes
            case Constants.CONSTANT_Class:
              final ConstantClass cconst = (ConstantClass)mconst;
              if (cconst.getNameIndex() > apos)
                cconst.setNameIndex(cconst.getNameIndex() - 1);
              break;
            case Constants.CONSTANT_Fieldref:
            case Constants.CONSTANT_InterfaceMethodref:
            case Constants.CONSTANT_Methodref:
              final ConstantCP frconst = (ConstantCP)mconst;
              if (frconst.getClassIndex() > apos)
                frconst.setClassIndex(frconst.getClassIndex() - 1);
              if (frconst.getNameAndTypeIndex() > apos)
                frconst.setNameAndTypeIndex(frconst.getNameAndTypeIndex() - 1);
              break;
            case Constants.CONSTANT_NameAndType:
              final ConstantNameAndType natconst = (ConstantNameAndType)mconst;
              if (natconst.getNameIndex() > apos)
                natconst.setNameIndex(natconst.getNameIndex() - 1);
              if (natconst.getSignatureIndex() > apos)
                natconst.setSignatureIndex(natconst.getSignatureIndex() - 1);
              break;
            case Constants.CONSTANT_String:
              final ConstantString strconst = (ConstantString)mconst;
              if (strconst.getStringIndex() > apos)
                strconst.setStringIndex(strconst.getStringIndex() - 1);
              break;
            default: //do nothing
          }
        }
      } //TODO the references in other structures must be updated (fields etc.)
      jc.getConstantPool().setConstantPool(consts);
    }
  }

  /**
   * Remove the given constant from the constants vector. It does not
   * recalculates references.
   *
   * @param apos the number of the constant to remove
   */
  public void justRemoveConstant(final int apos) {
    constants.remove(apos);
    if (apos < initialSize) {
      initialSize--;
      final Constant[] consts = new Constant[initialSize];
      for (int i = 0; i < initialSize; i++) {
        final Constant mconst = constants.get(i);
        consts[i] = mconst;
      }
      jc.getConstantPool().setConstantPool(consts);
    }
  }

  /**
   * This method replaces constant at index an_old_index with constant a_new.
   *
   * @param an_old_index an index of constant to replace
   * @param a_new a new constant
   */
  public void replaceConstant(final int an_old_index, final Constant a_new) {
    if (an_old_index > initialSize) {
      justRemoveConstant(an_old_index);
      addConstantAfter(a_new, an_old_index - 1, true);
    } else {
      justRemoveConstant(an_old_index);
      addConstantAfter(a_new, an_old_index - 1, false);
    }
  }

  public ConstantPool createCombinedCP() {
    final Vector vec = new Vector();
    final Constant[] cnst = jc.getConstantPool().getConstantPool();
    vec.ensureCapacity(cnst.length);
    vec.copyInto(cnst);
    vec.addAll(constants);
    final Constant [] cnst1 = (Constant[]) vec.toArray();
    final ConstantPoolGen cpg = new ConstantPoolGen(cnst1);
    return cpg.getFinalConstantPool();
  }
  
  /**
   * Removes this annotation from its container (i.e. class in case
   * the annotation is a class annotation or method in case the annotation
   * is a class annotation).
   */
  public void remove() {
    // TODO 
  }


  public void replaceWith(final IBCAttribute pa) {
    // TODO Auto-generated method stub
    
  }
}
