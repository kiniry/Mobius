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

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantCP;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantInteger;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantString;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ClassGen;
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
   * The representation of the combined constant pool.
   */
  private ConstantPoolGen combinedcp;

  /**
   * Number of constants in the first constant pool.
   */
  private int initialSize;

  /**
   * JavaClass related with it's primary constantPool,
   * used for {@link #reset()} method.
   */
  private final ClassGen jc;

  /**
   * BML class representation. (bcc.jc == jc).
   */
  private BCClassRepresentation bcc;

  /**
   * A standard constructor, from JavaClass. It inserts
   * constants from ordinary constant pool first, but it does
   * not read in the second constant pool. This waits until
   * the class attributes are read.
   *
   * @param ajc - {@link ClassGen} to initialize from.
   * @param classRepresentation the BML class representation
   * @throws ReadAttributeException - if second constant
   *     pool attribute format is invalid.
   */
  public BCConstantPool(final ClassGen ajc,
                        final BCClassRepresentation classRepresentation)
    throws ReadAttributeException {
    this.jc = ajc;
    this.bcc = classRepresentation;
    addStandardConstants(ajc.getConstantPool());
    final ConstantPoolGen cp = ajc.getConstantPool();
    this.initialSize = cp.getSize();
    this.combinedcp = new ConstantPoolGen(cp.getFinalConstantPool());
  }

  /**
   * Adds a constant to the first or second constant pool. If the constant
   * pool is <code>null</code> then the combined constant pool is
   * used as the reference for the constant from the first parameter.
   *
   * @param c - Constant to be added.
   * @param toSecondCP - <code>true</code> in case the constant should be
   *   added to the second constant pool, <code>false</code> in case this
   *   should be added to the first one
   * @param constantPoolGen in which the new constant is interpreted
   */
  public void addConstant(final Constant c,
                          final boolean toSecondCP,
                          final ConstantPoolGen constantPoolGen) {
    if (toSecondCP) {
      this.combinedcp.addConstant(c,
        constantPoolGen != null ? constantPoolGen : combinedcp);
    } else {
      addConstantAfter(c, initialSize - 1);
    }
  }

  /**
   * Adds a constant to the combined constant pool after the constant at the
   * given index. This method takes care of changing the number of indices
   * in constants.
   *
   * @param c - Constant to be added, indices should be as in the final
   *   constant pool
   * @param an_index - An index of the constant after which the constant should
   *   be added.
   */
  public void addConstantAfter(final Constant c, final int an_index) {
    reindexConstantPool(an_index + 1, combinedcp); //this reindexes the cp in jc
                                                   //as well
    addNoReindexing(an_index, c, combinedcp);
    if (an_index + 1 <= initialSize) {
      initialSize++;
      final ConstantPoolGen cpg = jc.getConstantPool();
      addNoReindexing(an_index, c, cpg);
    }
  }

  /**
   * Adds a constant to the constant pool after the constant at the given
   * index. This method does not take care of changing the number of indices
   * in constants.
   *
   * @param index An index of the constant after which the constant should
   *   be added
   * @param c the constant to add
   * @param cpg the constant pool to add the constant to
   */
  private void addNoReindexing(final int index, final Constant c,
                               final ConstantPoolGen cpg) {
    final int unusednum = getUnusedNum(cpg);
    final int oldsize = cpg.getSize();
    cpg.addConstant(c, cpg);
    if (cpg.getSize() == oldsize) {
      cpg.addConstant(new ConstantInteger(unusednum), cpg);
      cpg.setConstant(cpg.getSize() - 1, c);
    }
    final int size = cpg.getSize();
    for (int i = size - 1; i > index + 1; i--) {
      cpg.setConstant(i, cpg.getConstant(i - 1));
    }
    cpg.setConstant(index + 1, c);
  }

  /**
   * Seeks the first integer number which does not occur in the given constant
   * pool.
   *
   * @param cpg the constant pool to look the integers for
   * @return the first unused number
   */
  private static int getUnusedNum(final ConstantPoolGen cpg) {
    int num = 0;
    while (cpg.lookupInteger(num) >= 0) {
      num++;
    }
    return num;
  }

  /**
   * The method reindexes the constant pool entries so that the constant at the
   * given position can be added and all the constants with numbers starting
   * with the constant are shifted upwards.
   *
   * @param index the indices greater or equal should be incremented
   * @param cpg the constant pool to reindex constants in
   */
  private void reindexConstantPool(final int index,
                                   final ConstantPoolGen cpg) {
    for (int i = cpg.getSize() - 1; i > 0; i--) { // null in 0 always
      final Constant cnst = cpg.getConstant(i);
      if (cnst == null) continue; //this is possible in case Long or similar
                                  //constants are used
      switch (cnst.getTag()) { //reindexing
        case Constants.CONSTANT_Class:
          final ConstantClass ccnst = (ConstantClass) cnst;
          if (ccnst.getNameIndex() >= index)
            ccnst.setNameIndex(ccnst.getNameIndex() + 1);
          break;
        case Constants.CONSTANT_Fieldref:
        case Constants.CONSTANT_Methodref:
        case Constants.CONSTANT_InterfaceMethodref:
          final ConstantCP cfref = (ConstantCP) cnst;
          if (cfref.getClassIndex() >= index)
            cfref.setClassIndex(cfref.getClassIndex() + 1);
          if (cfref.getNameAndTypeIndex() >= index) {
            cfref.setNameAndTypeIndex(cfref.getNameAndTypeIndex() + 1);
          }
          break;
        case Constants.CONSTANT_String:
          final ConstantString cstr = (ConstantString) cnst;
          if (cstr.getStringIndex() >= index)
            cstr.setStringIndex(cstr.getStringIndex() + 1);
          break;
        case Constants.CONSTANT_Integer:
        case Constants.CONSTANT_Float:
        case Constants.CONSTANT_Long:
        case Constants.CONSTANT_Double:
        case Constants.CONSTANT_Utf8:
          break; //no reindexing needed
        case Constants.CONSTANT_NameAndType:
          final ConstantNameAndType cnat = (ConstantNameAndType) cnst;
          if (cnat.getNameIndex() >= index)
            cnat.setNameIndex(cnat.getNameIndex() + 1);
          if (cnat.getSignatureIndex() >= index) {
            cnat.setSignatureIndex(cnat.getSignatureIndex() + 1);
          }
          break;
        default:
          throw new ClassFormatException("Invalid byte tag in constant: " +
                                         cnst.getTag());
      }
    }
  }

  /**
   * Removes all entries from constant pool.
   * @author Tomasz Olejniczak (to236111@students.mimuw.edu.pl)
   */
  public void clearConstantPool() {
    //constants.clear();
    initialSize = 0;
    //addConstant(null, false);
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
    final int idx = combinedcp.lookupUtf8(cdata);
    if (idx >= 0) return idx;
    final int size = combinedcp.getSize();
    for (int i = 0; i < size; i++) {
      final Constant cnst = combinedcp.getConstant(i);
      if (cnst != null && cnst instanceof ConstantUtf8) {
        final String data = ((ConstantUtf8) cnst).getBytes();
        if (data.equals(cdata))
          return i;
      }
    }
    return -1;
  }

  /**
   * Searches for a NameAndType constant with two indices which are equal
   * to the ones given in the arguments.
   *
   * @param idx1 - the first (name) index
   * @param idx2 - the second (type) index
   * @return index of matching Constant or -1 if no
   *     Constant could be found.
   */
  public int findNATConstant(final int idx1, final int idx2) {
    final String name = ((ConstantUtf8)combinedcp.getConstant(idx1)).getBytes();
    final String signature = ((ConstantUtf8)combinedcp.getConstant(idx2)).
      getBytes();
    return combinedcp.lookupNameAndType(name, signature);
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
    return this.combinedcp.getConstant(i);
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
    final int n = this.combinedcp.getSize();
    if (n == this.initialSize) {
      return a_code;
    }
    a_code.append("\n" + DisplayStyle.SECOND_CONSTANT_POOL_KWD + "\n");
    for (int i = this.initialSize; i  <  n; i++) {
      a_code.append(printElement(i));
    }
    return a_code;
  }


//  /**
//   * Reinitializes constant pool from its Java class representation
//   * primary constant pool. The variables from the second constant
//   * pool are copied to the new constant pool.
//   */
//  public void reset() {
//    final int oldsize = getInitialSize();
//    final ConstantPoolGen ocpg = this.combinedcp;
//    this.combinedcp =
//      new ConstantPoolGen(this.jc.getConstantPool().getConstantPool());
//    addStandardConstants(combinedcp);
//    addStandardConstants(this.jc.getConstantPool());
//    this.initialSize = combinedcp.getSize();
//    for (int i = oldsize; i < ocpg.getSize(); i++) {
//      this.combinedcp.addConstant(ocpg.getConstant(i), ocpg);
//    }
//  }

  /**
   * Saves both constant pools to given JavaClass
   * (primary as an ordinary constant pool and secondary
   * as an "second constant pool" class attribute).
   *
   * @param ajc - JavaClass to save to.
   */
  public void save(final JavaClass ajc) {
    ajc.setConstantPool(jc.getConstantPool().getFinalConstantPool());
    final ByteArrayOutputStream baos = new ByteArrayOutputStream();
    final DataOutputStream file = new DataOutputStream(baos);
    try {
      file.writeShort(combinedcp.getSize() - this.initialSize);
      for (int i = this.initialSize; i  <  combinedcp.getSize(); i++) {
        this.combinedcp.getConstant(i).dump(file);
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

//  /**
//   * @return number of constants stored in both
//   *     constant pools.
//   */
//  public int size() {
//    return this.combinedcp.getSize();
//  }

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
      final int num = getUnusedNum(combinedcp);
      combinedcp.addInteger(num);
      this.combinedcp.setConstant(combinedcp.getSize() - 1, c);
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
    return combinedcp.getSize();
  }


  public void save(final AttributeWriter aw) {
    // TODO Auto-generated method stub
  }

  public ConstantPool createCombinedCP() {
    return combinedcp.getConstantPool();
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

  public ConstantPoolGen getConstantPool() {
    return jc.getConstantPool();
  }

  public ConstantPoolGen getCoombinedCP() {
    return combinedcp;
  }

  /**
   * Remove the given constant from the constants vector. It does not
   * recalculate references. The constants at indices higher than the
   * given one are moved to indices less by one.
   *
   * @param apos the number of the constant to remove
   */
  public void justRemoveConstant(final int apos) {
    //we assume the constant pool in jc and the combined constant pool
    //are synchronised
    final ConstantPoolGen fcp = jc.getConstantPool();
    if (apos < fcp.getSize()) {
      final ConstantPoolGen nfcp = justRemoveConstantFromCPG(fcp, apos);
      jc.setConstantPool(nfcp);
      initialSize--;
      final int numm = bcc.getMethodCount();
      for (int i = 0; i < numm; i++) {
        final BCMethod bcm = bcc.getMethod(i);
        bcm.setConstantPool(nfcp);
      }
    } // no else as we remove from both cpgs
    if (apos < combinedcp.getSize()) {
      combinedcp = justRemoveConstantFromCPG(combinedcp, apos);
    }
  }

  /**
   * Remove the given constant from the constant pool. It does not
   * recalculate references. The constants at indices higher than the
   * given one are moved to indices less by one.
   *
   * @param fcp the constant pool to remove constant from
   * @param pos the number of the constant to remove
   * @return a new constant pool with less entries by one
   */
  private static ConstantPoolGen justRemoveConstantFromCPG(
      final ConstantPoolGen fcp,
      final int pos) {
    for (int i = pos; i < fcp.getSize() - 1; i++) {
      fcp.setConstant(i, fcp.getConstant(i + 1));
    }
    final Constant[] cs = fcp.getConstantPool().getConstantPool();
    final Constant[] ncs = new Constant[cs.length - 1];
    System.arraycopy(cs, 0, ncs, 0, cs.length - 1);
    return new ConstantPoolGen(ncs);
  }

  /**
   * This method replaces constant at index an_old_index with constant a_new.
   *
   * @param an_old_index an index of constant to replace
   * @param a_new a new constant
   */
  public void replaceConstant(final int an_old_index, final Constant a_new) {
    if (an_old_index < initialSize) {
      jc.getConstantPool().setConstant(an_old_index, a_new);
    } // we update both cpgs
    if (an_old_index < combinedcp.getSize()) {
      combinedcp.setConstant(an_old_index, a_new);
    }
  }

  public int findFieldref(int classNameIndex, int nameAndTypeIndex) {
    final String class_name = ((ConstantUtf8)combinedcp.getConstant(classNameIndex)).getBytes();
    final ConstantNameAndType cnat = (ConstantNameAndType) (combinedcp.getConstant(nameAndTypeIndex));
    final String field_name = ((ConstantUtf8)combinedcp.getConstant(cnat.getNameIndex())).getBytes();
    return combinedcp.lookupFieldref(class_name, field_name, cnat.getSignature(combinedcp.getConstantPool()));
  }

}
