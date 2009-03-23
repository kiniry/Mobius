/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

import org.apache.bcel.classfile.AccessFlags;
import org.apache.bcel.generic.Type;

import annot.io.ReadAttributeException;

/**
 * This class contains the full functionality of a BML field. It allows to
 * access its structure, save and load field data from a class file,
 * pretty print its content, and parse textual representations.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BCField extends AccessFlags {

  /**
   * Serial version UID.
   */
  private static final long serialVersionUID = 1L;

  /**
   * The BML access flags for the variable.
   */
  private int myBMLFlags;

  /**
   * Points to field name in the second constant pool.
   */
  private int nameIndex;

  /**
   * Points to type descriptor the first or second constant pool.
   */
  private int descriptorIndex;

  /**
   * The combined first and second constant pools.
   */
  private BCConstantPool constantPool;

  /**
   * A constructor from already existing {@link BCField}. That
   * BCField should be used for operations on byte code
   * using the BCEL library.
   *
   * @param fd - BCField which represents the field information
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  public BCField(final BCField fd) throws ReadAttributeException {
    setAccessFlags(fd.getAccessFlags());
    myBMLFlags = fd.getBMLFlags();
    nameIndex = fd.getNameIndex();
    descriptorIndex = fd.getDescriptorIndex();
    constantPool = fd.getConstantPool();
  }


  /**
   * Returns the combined constant pool to identify the name and the type
   * of the field.
   *
   * @return the constant pool associated with the field
   */
  public BCConstantPool getConstantPool() {
    return constantPool;
  }


  /**
   * Returns the index to the combined constant pool of the type descriptor
   * of the field.
   *
   * @return the index of the type descriptor of the field
   */
  public int getDescriptorIndex() {
    return descriptorIndex;
  }


  /**
   * Returns the index to the combined constant pool of the name of the field.
   *
   * @return the index of the name of the field
   */
  public int getNameIndex() {
    return nameIndex;
  }


  /**
   * Returns the BML specific flags for the field.
   *
   * @return the flags
   */
  public int getBMLFlags() {
    return myBMLFlags;
  }


  public Type getType() {
    // TODO Auto-generated method stub
    return null;
  }

  public Object getName() {
    // TODO Auto-generated method stub
    return null;
  }
}
