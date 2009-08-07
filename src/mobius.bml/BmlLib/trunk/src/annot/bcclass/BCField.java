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
import org.apache.bcel.classfile.ClassFormatException;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.ConstantUtf8;
import org.apache.bcel.classfile.ConstantValue;
import org.apache.bcel.classfile.FieldOrMethod;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.classfile.Visitor;
import org.apache.bcel.generic.Type;

import annot.attributes.AttributeNames;
import annot.attributes.field.BMLModifierAttribute;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;

/**
 * This class contains the full functionality of a BML field. It allows to
 * access its structure, save and load field data from a class file,
 * pretty print its content, and parse textual representations.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BCField extends FieldOrMethod {

  /**
   * Serial version uid.
   */
  private static final long serialVersionUID = -4439716425203525886L;

  /**
   * A constant representing the information that the field is a normal Java
   * field.
   */
  public static final int JAVA_FIELD = 0;

  /**
   * A constant representing the information that the field is a ghost
   * field.
   */
  public static final int GHOST_FIELD = 1;

  /**
   * A constant representing the information that the field is a model
   * field.
   */
  public static final int MODEL_FIELD = 2;

  /**
   * The BML access flags for the variable.
   */
  private int myBMLFlags;

  /**
   * The BML field kind (ghost (={@link #GHOST_FIELD}) or model
   * (={@link MODEL_FIELD})).
   */
  private int myBMLKind;

  /**
   * The class in which the field resides.
   */
  private BCClass bcc;

  /**
   * The attributes of the current ghost field. Note that it contains all
   * the attributes except the {@link BMLModifierAttribute}.
   */
  private Attribute[] attributes = new Attribute[0];

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
    super(fd.getAccessFlags(), fd.getNameIndex(), fd.getDescriptorIndex(),
          fd.getAttributes(), fd.getConstantPool());
    setAccessFlags(fd.getAccessFlags());
    myBMLFlags = fd.getBMLFlags();
    setBMLKind(fd.getBMLKind());
    bcc = fd.getBMLClass();
    attributes = fd.getAttributes();
  }

  /**
   * A constructor from already existing {@link BCField}. That
   * BCField should be used for operations on byte code
   * using the BCEL library.
   *
   * @param abcc the class in which the field will be located
   */
  public BCField(final BCClass abcc) {
    super(0, -1, -1, null,
          abcc.getCp().getCoombinedCP().getFinalConstantPool());
    myBMLFlags = 0;
    bcc = abcc;
  }

  /**
   * Returns the combined constant pool to identify the name and the type
   * of the field.
   *
   * @return the constant pool associated with the field
   */
  public BCClass getBMLClass() {
    return bcc;
  }


  /**
   * Returns the index to the combined constant pool of the type descriptor
   * of the field.
   *
   * @return the index of the type descriptor of the field
   */
  public int getDescriptorIndex() {
    return getSignatureIndex();
  }


  /**
   * Sets the index to the combined constant pool of the type descriptor
   * of the field.
   *
   * @param idx the index to set
   */
  public void setDescriptorIndex(final int idx) {
    setSignatureIndex(idx);
  }


  /**
   * Returns the BML specific flags for the field.
   *
   * @return the flags
   */
  public int getBMLFlags() {
    return myBMLFlags;
  }

  /**
   * Sets the BML specific flags for the field.
   *
   * @param bmlFlags the flags to set
   */
  public void setBMLFlags(final int bmlFlags) {
    myBMLFlags = bmlFlags;
  }

  /**
   * @param aBMLKind the BML kind to set
   */
  public void setBMLKind(final int aBMLKind) {
    this.myBMLKind = aBMLKind;
  }

  /**
   * It gets the kind of BML field: {@link #JAVA_FIELD} means that the
   * field is a normal Java field, {@link #GHOST_FIELD} means that the
   * field is a ghost field, {@link #MODEL_FIELD} means that the field
   * is a model field.
   *
   * @return the kind of the BML field
   */
  public int getBMLKind() {
    return myBMLKind;
  }

  /**
   * @return the type of the current field
   */
  public Type getType() {
    final String tname = 
      ((ConstantUtf8)bcc.getCp().getConstant(getSignatureIndex())).getBytes();
    return Type.getType(tname);
  }

  /**
   * Set the name of the field adding it to the constant pool if necessary.
   *
   * @param name the string to which the name should be set
   */
  public void setName(final String name) {
    int idx = bcc.getCp().findConstant(name);
    if (idx < 0) {
      bcc.getCp().addConstant(new ConstantUtf8(name), myBMLKind != 0, null);
      idx = bcc.getCp().findConstant(name);
    }
    setNameIndex(idx);
  }

  /**
   * Set the type of the field. We check if the {@link Type} is in the
   * current constant pool. If necessary, its description is added there.
   *
   * @param typ the type of the field to be set
   */
  public void setType(final Type typ) {
    final String sig = typ.getSignature();
    int idx = bcc.getCp().findConstant(sig);
    if (idx < 0) {
      bcc.getCp().addConstant(new ConstantUtf8(sig),
                               myBMLKind != 0, null);
      idx = bcc.getCp().findConstant(sig);
    }
    setSignatureIndex(idx);
  }

  /**
   * This method saves the current field to the given writer. It uses the
   * fieldinfo structure as in Section 4.5 Fields of "The Java Virtual Machine
   * Specification":
   *   field_info {
   *     u2 access_flags;
   *     u2 name_index;
   *     u2 descriptor_index;
   *     u2 attributes_count;
   *     attribute_info attributes[attributes_count];
   *   }
   *
   * @param aw the writer to save the field to
   */
  public void save(final AttributeWriter aw) {
    aw.writeShort(getAccessFlags());
    aw.writeShort(getNameIndex());
    aw.writeShort(getSignatureIndex());
    if (myBMLFlags != 0) {
      aw.writeShort(attributes.length + 1);
      final BMLModifierAttribute bmmod =
        new BMLModifierAttribute(bcc, this);
      bmmod.save(aw);
    } else {
      aw.writeShort(attributes.length);
    }
    final ByteArrayOutputStream mbuf = new ByteArrayOutputStream();
    final DataOutputStream buf = new DataOutputStream(mbuf);
    final int idx1 = bcc.getCp().findConstant(
                       AttributeNames.FIELD_MODIFIERS_ATTR);
    for (int i = 0; i < attributes.length; i++) {
      try {
        final int idx = attributes[i].getNameIndex();
        if (idx != idx1) attributes[i].dump(buf);
      } catch (IOException e) {
        MLog.putMsg(MLog.LEVEL_PWARNING,
          "IOException in field saving. This should not happen");
      }
    }
    aw.writeBytes(mbuf.toByteArray());
  }

  /**
   * This method loads the current field from the given reader. It uses the
   * fieldinfo structure as in Section 4.5 Fields of "The Java Virtual Machine
   * Specification":
   *   field_info {
   *     u2 access_flags;
   *     u2 name_index;
   *     u2 descriptor_index;
   *     u2 attributes_count;
   *     attribute_info attributes[attributes_count];
   *   }
   *
   * @param ar the reader to read the data from
   * @throws ReadAttributeException 
   */
  public void load(final AttributeReader ar) throws ReadAttributeException {
    setAccessFlags(ar.readShort());
    setNameIndex(ar.readShort());
    setSignatureIndex(ar.readShort());
    final int len = ar.readShort();
    final ByteArrayInputStream mbuf = new ByteArrayInputStream(ar.getInput());
    final DataInputStream buf = new DataInputStream(mbuf);
    final Vector attrs = new Vector();
    final ConstantPool cp = bcc.getCp().createCombinedCP();
    final int idx1 = bcc.getCp().findConstant(
                        AttributeNames.FIELD_MODIFIERS_ATTR);
    for (int i = 0; i < len; i++) {
      Attribute attr;
      try {
        attr = Attribute.readAttribute(buf, cp);
        final int idx = attr.getNameIndex();
        if (idx == idx1) {
          final BMLModifierAttribute bmmod =
            new BMLModifierAttribute(bcc, this);
          final AttributeReader nar = new AttributeReader(bmmod);
          nar.readAttribute((Unknown)attr);
          myBMLFlags = bmmod.getModifiers();
          myBMLKind = GHOST_FIELD;
        } else {
          attrs.add(attr);
        }
      } catch (ClassFormatException e) {
        // TODO Auto-generated catch block 
        e.printStackTrace();
      } catch (IOException e) {
        // TODO Auto-generated catch block 
        e.printStackTrace();
      }
    }
    if (attrs.size() == 0) {
      attributes = new Attribute[0];
    } else {
      attributes = (Attribute[]) attrs.toArray();
    }
  }

  public void accept(Visitor obj) {
    // TODO Auto-generated method stub
    
  }

  public ConstantValue getConstantValue() {
    // TODO Auto-generated method stub
    return null;
  }

  public int setupCPEntries() {
    BCConstantPool bcp = bcc.getCp();
    if (getNameIndex() < 0 || getSignatureIndex() < 0)
      return -1;
    return bcp.getCoombinedCP().addFieldref(bcc.getBCELClass().getClassName(),
                                            getName(), getSignature());
  }
}
