/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.clazz;

import java.util.Iterator;
import java.util.Vector;

import org.apache.bcel.classfile.ConstantUtf8;

import annot.attributes.AttributeNames;
import annot.attributes.IBCAttribute;
import annot.bcclass.BCClass;
import annot.bcclass.BCField;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;

/**
 * This class represents GhostFields class attribute described in "GhostFields
 * Attribute" section of "BML Reference Manual".
 *
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class GhostFieldsAttribute implements ClassAttribute, IBCAttribute {

  /**
   * The class in which the current attribute resides.
   */
  private BCClass bcc;

  /**
   * The representation of the fields in the current class.
   */
  private Vector < BCField > ghostFields;

  /**
   * A constructor that creates the field based upon the class in which the
   * ghost fields are located.
   *
   * @param classRepresentation - BCClass containing this invariant,
   *   instance invariant
   */
  public GhostFieldsAttribute(final BCClass classRepresentation) {
    this.bcc = classRepresentation;
    if (classRepresentation.getCp().findConstant(getName()) == -1) {
      classRepresentation.getCp().addConstant(new ConstantUtf8(getName()),
        false, bcc.getCp().getConstantPool());
    }
    this.ghostFields = new Vector < BCField > ();
  }

  /**
   * Removes all the ghost fields from the class in which the current attribute
   * resides.  It removes in addition
   * the names and the NameAndType descriptors from the constant pool.
   */
  public void remove() {
    bcc.removeGhostFields();

  }

  /**
   * Replaces the {@link GhostFieldsAttribute} in the given
   * {@link BCClass} with the current attribute. At the same time it changes the
   * container class to the given one. This method updates
   * the constant pool.
   *
   * @param abcc the new location of the current attribute
   */
  public void replace(final BCClass abcc) {
    abcc.removeGhostFields();
    final Iterator i = ghostFields.iterator();
    ghostFields = new Vector < BCField > (ghostFields.size());
    while (i.hasNext()) {
      final BCField fd = (BCField) i.next();
      final BCField nfd = new BCField(abcc);
      nfd.setAccessFlags(fd.getAccessFlags());
      nfd.setBMLFlags(fd.getBMLFlags());
      nfd.setBMLKind(fd.getBMLKind());
      nfd.setName(fd.getName());
      nfd.setType(fd.getType());
      ghostFields.add(nfd);
    }
    abcc.setGhostFields(this);
  }

  /**
   * Replaces this annotation with a given one, updating
   * necessary references in BCClass.
   *
   * @param pa - annotation to replace with.
   */
  public void replaceWith(final IBCAttribute pa) {
    ((ClassAttribute)pa).replace(bcc);
  }

  /**
   * A simple textual representation for debugging purposes. It just prints
   * out the array of ghost field names.
   *
   * @return a simple String representation of all the ghost fields
   */
  public String toString() {
    final StringBuffer buf = new StringBuffer();
    buf.append("GhostFields=[ ");
    final Iterator i = ghostFields.iterator();
    boolean mark = false;
    while (i.hasNext()) {
      if (mark) {
        buf.append(", ");
        mark = true;
      }
      buf.append(i.next().toString());
    }
    buf.append(']');
    return buf.toString();
  }

  /**
   * @return the index in the constant pool of the attribute name or -1
   *   in case the name is not in the constant pool
   */
  public int getIndex() {
    return this.bcc.getCp().findConstant(AttributeNames.GHOST_FIELDS_ATTR);
  }


  /**
   * @return return the attribute name as used in class files to identify
   *   it
   */
  public String getName() {
    return AttributeNames.GHOST_FIELDS_ATTR;
  }


  /**
   * A structure with ghost fields is saved. The format
   *
   *   u2 fields_count;
   *   fieldinfo fields[fields_count];
   *
   * is used which is described in "GhostFields Attribute" section of
   * "BML Reference Manual".
   *
   * @param aw the writer to write the attribute to
   */
  public void save(final AttributeWriter aw) {
    aw.writeShort(ghostFields.size());
    final Iterator i = ghostFields.iterator();
    while (i.hasNext()) {
      final BCField fd = (BCField) i.next();
      fd.save(aw);
    }
  }

  /**
   * A structure with ghost fields is loaded. The format
   *
   *   u2 fields_count;
   *   fieldinfo fields[fields_count];
   *
   * is used which is described in "GhostFields Attribute" section of
   * "BML Reference Manual".
   *
   * @param ar the reader to read the attribute from
   * @throws ReadAttributeException in case part of the attribute cannot be
   *   read due to malformed structure
   */
  public void load(final AttributeReader ar)
    throws ReadAttributeException {
    final int size = ar.readShort();
    ghostFields = new Vector < BCField > ();
    for (int i = 0; i < size; i++) {
      final BCField fd = new BCField(bcc);
      fd.load(ar);
      fd.setBMLKind(BCField.GHOST_FIELD);
      ghostFields.add(fd);
    }
  }

  /**
   * This method removes given BML field with the name matching the name
   * of the given field from the current table of BML fields.
   *
   * @param afield the field to remove
   */
  public void removeBMLField(final BCField afield) {
    final Iterator i = ghostFields.iterator();
    while (i.hasNext()) {
      final BCField of = (BCField) i.next();
      if (of.getNameIndex() == afield.getNameIndex()) {
        i.remove();
      }
    }
  }

  /**
   * @return the number of fields in the current attribute
   */
  public int size() {
    return ghostFields.size();
  }

  /**
   * Returns the BML field of the given index.
   *
   * @param i the number of the field
   * @return the field under the given number
   */
  public BCField get(final int i) {
    return ghostFields.get(i);
  }

  /**
   * This method adds the given field to the current attribute with the ghost
   * fields.
   *
   * @param afield the field to add
   */
  public void add(final BCField afield) {
    ghostFields.add(afield);
  }

  /**
   * The iterator which allows to operate on all the fields in the current
   * attribute.
   *
   * @return the iterator over fields
   */
  public Iterator < BCField > iterator() {
    return ghostFields.iterator();
  }

}
