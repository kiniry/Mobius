/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.field;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.Unknown;

import annot.attributes.AttributeNames;
import annot.attributes.IBCAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCField;
import annot.bcclass.BMLModifiersFlags;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.DisplayStyle;

/**
 * This class represents BML field attributes with BML field modifiers.
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BMLModifierAttribute implements IBCAttribute {

  /**
   * BCClass containing this attribute.
   */
  private BCClass bcc;

  /**
   * The Java field which contains this attribute. This is non-null only
   * in case the modifier is associated with a Java field.
   */
  private Field field;

  /**
   * The BML field which contains this attribute. This is non-null only
   * in case the modifier is associated with a BML model or ghost field.
   */
  private BCField bfield;

  /**
   * The BML modifiers in this attribute.
   */
  private int modifiers = BMLModifiersFlags.BML_NONE;

  /**
   * The field indicates if the attribute is read.
   */
  private boolean isRead;

  /**
   * The constructor which assembles the BMLModifierAttribute based on the
   * class in which the attribute resides and the modifiers which it represents.
   *
   * @param abcc the class for this attribute
   * @param abfield the BML field for which the modifiers are held in this
   *   attribute
   */
  public BMLModifierAttribute(final BCClass abcc, final BCField abfield) {
    bcc = abcc;
    modifiers = abfield.getBMLFlags();
    bfield = abfield;
  }

  /**
   * The constructor creates the modifier for the given field in the given
   * class. It reads in the value of the modifier from the attributes of
   * the field. In case there are no BML modifier attribute in the field
   * the default modifiers (0) are assumed.
   *
   * @param afield the field for which the modifier is created
   * @param classRepresentation the class in which the field and the modifier
   *   reside
   * @throws ReadAttributeException - if the structure of one of field's
   *   the attributes is found not to be correct
   */
  public BMLModifierAttribute(final Field afield,
                              final BCClass classRepresentation)
    throws ReadAttributeException {
    bcc = classRepresentation;
    field = afield;
    readModifiers(afield.getAttributes());
  }

  /**
   * Reads in the BML modifiers attributes from the given array of attributes.
   * This is supposed to be an array of field attributes. Only first modifier
   * attribute is taken into account as stated in section "FieldModifiers
   * Attribute" in "BML Reference Manual".
   *
   * @param attributes the attributes to read modifiers from.
   * @throws ReadAttributeException - if the structure of one of the attributes
   *   is not correct
   */
  private void readModifiers(final Attribute[] attributes)
    throws ReadAttributeException {
    final AttributeReader ar = new AttributeReader(this);
    for (int i = 0; i < attributes.length; i++) {
      if (attributes[i] instanceof Unknown) {
        final Unknown new_name = (Unknown) attributes[i];
        ar.readAttribute(new_name);
        if (isRead) return; //Only first attribute is taken into account
      }
    }
    return;
  }

  /**
   * Returns the index in the constant pool to the name of the Utf8 constant
   * with the name of the current attribute. It does not check if the name
   * exists in the constant pool.
   *
   * @return index in the constant pool to the name of the Utf8 constant with
   *   the name of the current attribute
   */
  public int getIndex() {
    return this.bcc.getCp().findConstant(AttributeNames.FIELD_MODIFIERS_ATTR);
  }

  /**
   * The name of the attribute stored in the constant pool.
   *
   * @return the name of the current attribute
   */
  public String getName() {
    return AttributeNames.FIELD_MODIFIERS_ATTR;
  }

  /**
   * Saves this annotation to BCEL's Unknown attribute using attributeWriter.
   *
   * @param aw - stream to save the attribute to
   */
  public void save(final AttributeWriter aw) {
    aw.writeInt(modifiers);
  }

  /**
   * Loads this annotation from BCEL's Unknown attribute using attributeReader.
   *
   * @param ar - stream to load from
   * @throws ReadAttributeException not thrown in this case
   */
  public void load(final AttributeReader ar) throws ReadAttributeException {
    modifiers = ar.readInt();
    isRead = true;
  }

  /**
   * Displays content of the current modifiers. We assume that the array
   * {@link BMLModifiersFlags#BML_MODIFIERS} is in sync with the array
   * {@link DisplayStyle}{@link #BML_MODIFIERS}.
   *
   * @return String representation of the current modifiers
   */
  @Override
  public String toString() {
    return printBMLModifiers(modifiers);
  }

  /**
   * Displays content of the current modifiers. We assume that the array
   * {@link BMLModifiersFlags#BML_MODIFIERS} is in sync with the array
   * {@link DisplayStyle}{@link #BML_MODIFIERS}.
   *
   * @param modifiers the modifiers to print out
   * @return String representation of the current modifiers
   */
  public static String printBMLModifiers(final int modifiers) {
    final StringBuffer buf = new StringBuffer("");
    for (int i = 0; i < BMLModifiersFlags.BML_MODIFIERS.length; i++) {
      if ((modifiers & BMLModifiersFlags.BML_MODIFIERS[i]) != 0) {
        if (buf.length() > 0) {
          buf.append(" ");
        }
        buf.append(DisplayStyle.BML_MODIFIERS[i]);
      }
    }
    return buf.toString();
  }

  /**
   * @param themodifiers the BML modifiers to set
   */
  public void setModifiers(final int themodifiers) {
    this.modifiers = themodifiers;
  }

  /**
   * @return the BML modifiers in the attribute
   */
  public int getModifiers() {
    return modifiers;
  }

  /**
   * Removes this annotation from its container in this case {@link BCClass}
   * in case the modifier is a Java field BML modifier or from {@link BCField}
   * in case the modifier is a BML field BML modifier.
   */
  public void remove() {
    if (field != null) {
      setModifiersForJavaField(BMLModifiersFlags.BML_NONE);
    }
    if (bfield != null) {
      bfield.setModifiers(BMLModifiersFlags.BML_NONE);
    }
  }

  /**
   * Sets given modifiers for the current Java field in the current
   * {@link BCClass}. It assumes that the field is in the fields
   * array of the class.
   *
   * @param modif the modifiers to set
   */
  private void setModifiersForJavaField(final int modif) {
    final Field[] fds = bcc.getBCELClass().getFields();
    for (int i = 0; i <= fds.length; i++) {
      if (fds[i] == field) {
        final BMLModifierAttribute bmod = bcc.getBMLModifierForField(i);
        bmod.setModifiers(modif);
      }
    }
  }

  /**
   * Replaces the modifiers associated with the current field with the
   * ones from the given attribute. Note that this method does not change
   * the actual objects the representation operates on, but it changes their
   * content.
   *
   * @param pa the attribute with modifiers to set
   */
  public void replaceWith(final IBCAttribute pa) {
    if (pa instanceof BMLModifierAttribute) {
      final BMLModifierAttribute bmod = (BMLModifierAttribute) pa;
      if (field != null)
        setModifiersForJavaField(bmod.getModifiers());
      if (bfield != null)
        bfield.setBMLFlags(bmod.getModifiers());
    }
  }
}
