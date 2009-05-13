/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2009 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;

import org.apache.bcel.generic.InstructionHandle;

import annot.attributes.AType;
import annot.attributes.method.AssertTable;
import annot.attributes.method.InCodeAnnotation;
import annot.attributes.method.LoopSpecificationTable;
import annot.attributes.method.SingleAssert;
import annot.attributes.method.SingleList;
import annot.attributes.method.SingleLoopSpecification;

/**
 * This class represents collection of all annotations inside
 * <code>method</code>'s body (one BCAttributeMap for each method).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @version a-01
 */
public class BCAttributeMap {

  /**
   * Method's attribute used for loading asserts from
   * and saving them to .class file (to BCEL method).
   */
  private final AssertTable atab;

  /**
   * Single annotations count.
   * May be out of date, use getLength() instead!
   */
  @Deprecated
  private int length;

  /**
   * Method's attribute used for loading loop specifications
   * from and saving them to .class file (to BCEL method).
   */
  private final LoopSpecificationTable lstab;

  /**
   * Hash map containing lists of annotations for each
   * instruction in the method.
   */
  private final HashMap < InstructionHandle, SingleList >  map;

  /**
   * The method mentioned in headers comment.
   */
  private final BCMethod method;

  /**
   * Constructor from a method that creates
   * an empty collection.
   *
   * @param m - the method.
   */
  public BCAttributeMap(final BCMethod m) {
    this.method = m;
    this.atab = new AssertTable(m, this);
    this.lstab = new LoopSpecificationTable(m, this);
    this.length = 0;
    this.map = new HashMap < InstructionHandle, SingleList > ();
  }

  /**
   * Adds an annotation to the collection (as an last
   * annotation for it's instruction).
   *
   * @param ica - an attribute to be added.
   */
  public void addAttribute(final InCodeAnnotation ica) {
    addAttribute(ica, -1);
  }

  /**
   * Adds an annotation with given minor number to the
   * collection.
   *
   * @param ica - annotation to be added. Must have set
   *     ih (instructionHandle) attribute,
   * @param minor - position of annotation within
   *     its instruction. Annotation will be inserted
   *     after last annotation for its instruction
   *     with less or equal minor number than this
   *     parameter.
   */
  public void addAttribute(final InCodeAnnotation ica, final int minor) {
    if (ica.getIh() == null) {
      throw new RuntimeException("InstructionHandle not set");
    }
    ica.setMinor(minor);
    if (this.map.containsKey(ica.getIh())) {
      this.map.get(ica.getIh()).addAttribute(ica);
    } else {
      final SingleList sl = new SingleList(this.method, ica.getIh());
      sl.addAttribute(ica);
      this.map.put(ica.getIh(), sl);
    }
    this.length++;
  }

  /**
   * Adds an empty annotation of given type, pc and minor.
   *
   * @param atype - type of annotation
   *     (from AType interface),
   * @param pc - current pc number of instruction to add
   *     new annotation before,
   * @param minor - minor number of inserted annotation
   *     (for annotation ordering for single instruction).
   * @return inserted annotation.
   */
  @Deprecated
  public InCodeAnnotation addAttribute(final int atype, final int pc,
                                      final int minor) {
    switch (atype) {
      case AType.C_ASSERT:
        final SingleAssert sa = new SingleAssert(this.method,
          this.method.findAtPC(pc), minor);
        addAttribute(sa, minor);
        return sa;
      case AType.C_LOOPSPEC:
        final SingleLoopSpecification sls = new SingleLoopSpecification(
          this.method, this.method.findAtPC(pc), minor, null, null);
        addAttribute(sls, minor);
        return sls;
      default:
        throw new RuntimeException("invalid attribute type");
    }
  }

  /**
   * Returns lists of all annotations for given instruction.
   *
   * @param ih - given instruction handle.
   * @return SingleList of annotation for given instruction
   *     (or an new empty list if there are no annotations
   *     for given instruction).
   */
  public SingleList getAllAt(final InstructionHandle ih) {
    final SingleList sl = this.map.get(ih);
    if (sl == null) {
      return new SingleList(this.method, ih); //XXX new?
    }
    return sl;
  }

  /**
   * Gives all annotations of given type from the collection.
   *
   * @param types - attribute types mask (from ATypes).
   * @return array of annotations matching given type mask.
   */
  public InCodeAnnotation[] getAllAttributes(final int types) {
    final InCodeAnnotation[] all =
      new InCodeAnnotation[getAttributeCount(types)];
    final LinkedList < SingleList >  ll = new LinkedList < SingleList > ();
    final Iterator < SingleList >  iter1 = this.map.values().iterator();
    while (iter1.hasNext()) {
      ll.addLast(iter1.next());
    }
    Collections.sort(ll);
    final Iterator < SingleList >  iter = ll.iterator();
    int i = 0;
    while (iter.hasNext()) {
      final SingleList sl = iter.next();
      final InCodeAnnotation[] some = sl.getAll(types);
      for (int j = 0; j  <  some.length; j++) {
        all[i++] = some[j];
      }
    }
    return all;
  }

  /**
   * @return assert table for file I/O.
   */
  public AssertTable getAtab() {
    return this.atab;
  }

  /**
   * Gives the number of the attributes with a particular type. The types
   * are described in {@link AType}.
   *
   * @param types the type of attributes to calculate the number for
   * @return the number of the attributes that match the given type
   */
  public int getAttributeCount(final int types) {
    int cnt = 0;
    final Iterator < SingleList >  iter1 = this.map.values().iterator();
    while (iter1.hasNext()) {
      cnt += iter1.next().getAttributeCount(types);
    }
    return cnt;
  }

  /**
   * Computes total count of annotations in this map.
   *
   * @return total annotation count.
   */
  public int getLength() {
    int l = 0;
    final Iterator < SingleList >  iter1 = this.map.values().iterator();
    while (iter1.hasNext()) {
      l += iter1.next().size();
    }
    return l;
  }

  /**
   * Returns the current loop specification table.
   *
   * @return the current loop specification table
   */
  public LoopSpecificationTable getLstab() {
    return this.lstab;
  }

  /**
   * Clears the collection (removes all annotations).
   */
  public void removeAll() {
    final Iterator < SingleList >  iter = this.map.values().iterator();
    while (iter.hasNext()) {
      final SingleList sl = iter.next();
      sl.removeAll();
    }
    this.map.clear();
    this.length = 0;
  }

  /**
   * Removes given annotation from the collection.
   *
   * @param ica - annotation to be removed.
   */
  public void removeAttribute(final InCodeAnnotation ica) {
    if (!this.map.containsKey(ica.getIh())) {
      throw new RuntimeException("attribute not found!");
    }
    this.map.get(ica.getIh()).removeAttribute(ica);
    this.length--;
  }

  /**
   * Replaces given annotations from this collection
   * with another one. New annotation will be placed
   * in the same place as the old one, regardless of
   * its ih and minor attributes.
   *
   * @param olda - annotation to be removed,
   * @param newa - annotation to be inserted
   *     in <code>olda</code>'s place.
   */
  public void replaceAttribute(final InCodeAnnotation olda,
                               final InCodeAnnotation newa) {
    if (!this.map.containsKey(olda.getIh())) {
      throw new RuntimeException("attribute not found!");
    }
    newa.setIh(olda.getIh());
    newa.setMinor(olda.getMinor());
    final SingleList sl = this.map.get(olda.getIh());
    sl.replace(olda, newa);
  }

  /**
   * Replaces current annotation list for given instruction
   * handle with given one.
   *
   * @param ih - instruction whose annotation list should
   *     be replaced,
   * @param sl - new annotations list.
   */
  public void setAtributesForInstruction(final InstructionHandle ih,
                                         final SingleList sl) {
    MLog.putMsg(MessageLog.LEVEL_PINFO, "singleList replaced");
    this.map.put(ih, sl);
  }

}
