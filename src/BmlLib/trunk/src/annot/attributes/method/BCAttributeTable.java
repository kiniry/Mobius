/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.attributes.method;

import annot.attributes.IBCAttribute;
import annot.bcclass.BCAttributeMap;
import annot.bcclass.BCMethod;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;

/**
 * This class represents method attribute for loading from
 * / saving to BCEL Unknown method's attribute (and then
 * to .class file) using attributeReader/attributeWriter.
 * It don't store any annotations, but operate on ones
 * in BCAttributeMap.
 * (one BCAttribute table for each type of annotations
 * for each method)
 *
 * The class handles the operation on:
 * <ul>
 *   <li> {@link AssertTable}
 *   <li> {@link LoopSpecificationTable}
 *   <li> others (TODO: define explicitly as they start to be
 *        handled)
 * </ul>
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public abstract class BCAttributeTable implements IBCAttribute {

  /**
   * The method in which the attribute resides.
   */
  private final /*@ non_null@*/ BCMethod method;

  /**
   * and it's annotation collection.
   */
  private final BCAttributeMap parent;

  /**
   * A constructor from method and it's BCAttributeMap.
   * BCAttributeTable operates on <code>parent</code>'s
   * annotations, it don't store any annotations itself.
   *
   * @param m - the method,
   * @param aparent - it's annotation's collection.
   */
  public BCAttributeTable(final BCMethod m, final BCAttributeMap aparent) {
    this.method = m;
    this.parent = aparent;
  }

  /**
   * @return nameIndex of BCEL's Unknown
   *     attribute it represents.
   */
  public int getIndex() {
    return this.method.getBcc().getCp().findConstant(getName());
  }

  /**
   * @return Unknown (BCEL) attribute name.
   */
  public abstract String getName();

  /**
   * Loads all annotations from BCEL's Unknown method
   * attribute to BCAttributeMap (<code>parent</code>),
   * using attributeReader.
   *
   * The loading follows the general pattern:
   * {
   *    u2 point_pc;
   *    u2 index;
   *    specific_info specific;
   * }
   * where the field specific contains an attribute specific
   * data which in some cases may be empty. An example of such a specification
   * is described in the section  AssertTable Attribute of "BML Reference
   * Manual".
   *
   * @param ar - stream to load annotations from.
   * @throws ReadAttributeException - if data left
   *     in <code>ar</code> doesn't represent correct
   *     annotation.
   */
  public void load(final AttributeReader ar) throws ReadAttributeException {
    final int n = ar.readItemsCount();
    for (int i = 0; i  <  n; i++) {
      final int pc = ar.readShort();
      final int minor = ar.readShort();
      final InCodeAnnotation ica = loadSingle(this.method, ar);
      ica.setIh(this.method.findAtPC(pc));
      ica.setMinor(minor);
      if (ica.getIh() == null) {
        throw new ReadAttributeException("Attribute unplaceble: pc=" + pc);
      }
      this.parent.addAttribute(ica); //this should be removed if we uncomment
                                     //next instruction.
      //      parent.addAttribute(ica, minor);
    }
  }

  /**
   * Loads a single annotation from file in case many annotations of a
   * particular kind can reside in a table or array.
   *
   * @param m - method containing this attribute,
   * @param ar - stream to load from.
   * @return a single attribute loaded from the given attribute reader
   * @throws ReadAttributeException if data left in <code>ar</code> does not
   *   represent a correct attribute
   */
  protected abstract InCodeAnnotation loadSingle(BCMethod m, AttributeReader ar)
    throws ReadAttributeException;

  /**
   * Saves all annotations from BCAttributeMap
   * (<code>parent</code>) of this type to BCEL's Unknown
   * method attribute using AttributeWriter. The type
   * of annotations saved to Unknown attribute is determined
   * by subclasses.
   *
   * The saving follows the general pattern:
   * {
   *    u2 point_pc;
   *    u2 index;
   *    specific_info specific;
   * }
   * where the field specific contains an attribute specific
   * data which in some cases may be empty. An example of such a specification
   * is described in the section  AssertTable Attribute of "BML Reference
   * Manual"
   *
   * @param aw - stream to save annotations to.
   */
  public void save(final AttributeWriter aw) {
    aw.writeAttributeCount(this.parent.getAttributeCount(singleType()));
    final InCodeAnnotation[] all = this.parent.getAllAttributes(singleType());
    for (int i = 0; i  <  all.length; i++) {
      aw.writeShort(all[i].getPC());
      aw.writeShort(all[i].getMinor());
      saveSingle(all[i], aw);
    }
  }

  /**
   * Saves a single annotation to a file in case many annotations of a
   * particular kind can reside in a table or array.
   *
   * @param icannot method containing this annotation
   * @param aw stream to write the annotation to
   */
  protected abstract void saveSingle(final InCodeAnnotation icannot,
                                     final AttributeWriter aw);

  /**
   * Returns the attribute type for the given attribute. The type is used
   * as a property to filter annotations of a particular kind in the
   * {@link BCAttributeMap} which contains the annotations associated with
   * the current method.
   *
   * @return attribute type of single annotation.
   */
  protected abstract int singleType();

}
