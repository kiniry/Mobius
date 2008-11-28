/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

import java.io.IOException;
import java.util.Collection;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.ConstantPool;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;

import annot.attributes.AType;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.ClassInvariant;
import annot.attributes.InCodeAttribute;
import annot.bcexpression.BCExpression;
import annot.bcexpression.util.ExpressionWalker;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.modifiers.BMLModifier;
import annot.textio.DisplayStyle;
import bmllib.utils.FileUtils;

/**
 * This class is an abstract representation of represents a bytecode class.
 * This class can be used to manipulate BML annotations, while operation on
 * bytecode itself can be performed using methods from BCEL library,
 * but BCEL's object should be accessed via this class.
 *
 * JavaClass from this object (jc field) should be
 * the same as JavaClass used for performing operations on
 * bytecode using BCEL library. Also all BCEL methods should
 * be accessed (or at least be the same) as the ones in this class
 * (getMethod(index).getBCELMethod()).
 *
 * This abstract class handles the accessors to all the class components and
 * handle loading and saving the class to a file.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public abstract class BCClassRepresentation {


  /**
   * Constant pool (including second constant pool's constants).
   */
  private BCConstantPool cp;

  /**
   * BML invariants. The key is here the access flags and the
   * value is the invariant for the access flags.
   */
  private final Hashtable invariants = new Hashtable();

  /**
   * BCEL's JavaClass for this class, for bytecode
   * operations.
   */
  private JavaClass jc;

  /**
   * Array with methods.
   */
  private BCMethod[] methods;

  /**
   * The BML modifiers for fields in the class.
   */
  private BMLModifier[] bml_fmodifiers;


  /**
   * Removes all Attributes used by this library from
   * given array.
   *
   * @param arr - an array of BCEL's Attributes.
   * @return <code>arr</code> with all BML attributes
   *     removed.
   */
  public static Attribute[] removeBMLAttributes(final Attribute[] arr) {
    final Vector < Attribute >  v = new Vector < Attribute > ();
    for (int i = 0; i  <  arr.length; i++) {
      if (arr[i] instanceof Unknown) {
        final Unknown ua = (Unknown) arr[i];
        final String aname = ua.getName();
        if (DisplayStyle.INVARIANTS_ATTR.equals(aname)) {
          continue;
        }
        if (DisplayStyle.METHOD_SPECIFICATION_ATTR.equals(aname)) {
          continue;
        }
        if (DisplayStyle.ASSERT_TABLE_ATTR.equals(aname)) {
          continue;
        }
        if (DisplayStyle.LOOP_SPECIFICATION_TABLE.equals(aname)) {
          continue;
        }
      }
      v.add(arr[i]);
    }
    final Attribute[] attrs = new Attribute[v.size()];
    for (int i = 0; i  <  attrs.length; i++) {
      attrs[i] = v.elementAt(i);
    }
    return attrs;
  }

  /**
   * Adds Unknown class attribute to BCEL's Attribute array,
   * or replaces one from array if it has the same name and
   * the same access flags.
   *
   * @param arr - array of BCEL's Attributes,
   * @param ua - BCEL's Unknown attribute to be added.
   * @return <code>arr</code> with <code>ua</code> inserted.
   */
  public static Attribute[] addAttribute(final Attribute[] arr,
                                         final Unknown ua) {
    final int n = arr.length;
    for (int i = 0; i  <  n; i++) {
      if (arr[i] instanceof Unknown) {
        final Unknown catr = (Unknown) arr[i];
        final String aname = catr.getName();
        final int access_flags1 = (catr.getBytes()[0] << Byte.SIZE) |
          catr.getBytes()[1];
        final int access_flags2 = (ua.getBytes()[0] << Byte.SIZE) |
          ua.getBytes()[1];
        if (aname.equals(ua.getName()) && access_flags1 == access_flags2) {
          arr[i] = ua;
          return arr;
        }
      }
    }
    final Attribute[] a2 = new Attribute[n + 1];
    for (int i = 0; i  <  n; i++) {
      a2[i] = arr[i];
    }
    a2[n] = ua;
    return a2;
  }

  /**
   * @return constant pool (from this library, not
   * BCEL's one)
   */
  public BCConstantPool getCp() {
    return this.cp;
  }

  /**
   * Adds a BML class annotation to this class.
   * If given annotation is a method annotation,
   * nothing happens.
   *
   * @param pa - annotation to be added.
   * @return if <code>pa</code> is an BML class attribute.
   */
  public boolean addAttribute(final BCPrintableAttribute pa) {
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "adding class attribute: " +
                pa.toString());
    if (pa instanceof ClassInvariant) {
      final ClassInvariant inv = (ClassInvariant) pa;
      final Integer access = Integer.valueOf(inv.getAccessFlags());
      this.invariants.put(access, inv);
      return true;
    }
    return false;
  }

  /**
   * Returns the invariant for the given access flags specifications.
   * Possible access flags are defined in {@link BMLModifiersFlags}.
   *
   * @param accessflags the access flags for which the invariant should
   *   be retrieved
   * @return class invariant for the given access flags
   */
  public ClassInvariant getInvariant(final int accessflags) {
    return (ClassInvariant) this.invariants.get(Integer.valueOf(accessflags));
  }

  /**
   * Returns the enumerator over all the invariants.
   *
   * @return class invariant enumerator
   */
  public Enumeration getInvariantEnum() {
    return this.invariants.elements();
  }

  /**
   * Adds class invariant.
   *
   * @param inv - new class invariant.
   */
  public void setInvariant(final ClassInvariant inv) {
    final Integer af = Integer.valueOf(inv.getAccessFlags());
    this.invariants.put(af, inv);
  }

  /**
   * @return BCEL's JavaClass
   */
  public JavaClass getJC() {
    return this.jc;
  }

  /**
   * @param index - index of method (position in string
   *     representation of bytecode), starting from 0
   *     (including  &lt;clinit&gt;  and  &lt;init&gt; , if any).
   * @return BCMethod of given index.
   */
  public BCMethod getMethod(final int index) {
    return this.methods[index];
  }

  /**
   * @return number of BCMethods in this class.
   */
  public int getMethodCount() {
    return this.methods.length;
  }


  /**
   * Initialize BCClass and read BML attributes from
   * given JavaClass.
   *
   * @param ajc - JavaClass to initialize from.
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  protected void load(final JavaClass ajc) throws ReadAttributeException {
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "initializing bcclass");
    this.jc = ajc;
    this.cp = new BCConstantPool(ajc);

    MLog.putMsg(MessageLog.LEVEL_PINFO, "  loading class attributes");
    final Attribute[] attrs = ajc.getAttributes();
    final AttributeReader ar = getFreshAttributeReader();
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        ar.readAttribute((Unknown) attrs[i]);
      }
    }

    final Field[] fields = ajc.getFields();
    this.bml_fmodifiers = new BMLModifier[fields.length];
    for (int i = 0; i  <  fields.length; i++) {
      this.bml_fmodifiers[i] = getFreshFieldMod(fields[i]);
    }

    final Method[] mtab = ajc.getMethods();
    this.methods = new BCMethod[mtab.length];
    for (int i = 0; i  <  mtab.length; i++) {
      this.methods[i] = getFreshMethod(mtab[i], ajc.getClassName(),
                                       ajc.getConstantPool());
    }
  }

  private BMLModifier getFreshFieldMod(Field field) throws ReadAttributeException {
    return new BMLModifier(field, this);
  }

  /**
   * Creates the BMLLib representation of the given method in the class of the
   * given name and with the given constant pool. This method may parse the
   * BML related attributes inside the method. The actual execution is delegated
   * to the final subclass which has the full functionality of BML class.
   *
   * @param meth the BCEL method based on which the BMLLib method is generated
   * @param clname the name of the class in which the method is located
   * @param cpool the constant pool
   * @return the BMLLib method representation
   * @throws ReadAttributeException in case some of the BML attributes wasn't
   *   correctly parsed by BMLLib
   */
  protected abstract BCMethod getFreshMethod(final Method meth,
                                             final String clname,
                                             final ConstantPool cpool)
    throws ReadAttributeException;

  /**
   * Creates a fresh BMLLib attribute reader. The actual execution is delegated
   * to the final subclass which has the full functionality of BML class.
   *
   * @return the BMLLib attribute reader
   */
  protected abstract AttributeReader getFreshAttributeReader();

  /**
   * Searches constant pool for index of this class'es field
   * of given name.
   *
   * @param fieldName - name of a field in this class.
   * @return field's index, for use in
   *     {@link FieldRef#FieldRef(boolean, BCConstantPool, int)},<br>
   *     or <b>-1</b> if this class has no fields of given name.
   */
  public int getFieldIndex(final String fieldName) { // O(n)
    final Field[] ftab = this.jc.getFields();
    for (int i = 0; i  <  ftab.length; i++) {
      if (fieldName.equals(ftab[i].getName())) {
        final int ni = ftab[i].getNameIndex();
        final Constant[] ctab = this.jc.getConstantPool().getConstantPool();
        for (int j = 0; j  <  ctab.length; j++) {
          if (ctab[j] instanceof ConstantNameAndType) {
            final ConstantNameAndType cnt = (ConstantNameAndType) ctab[j];
            if (cnt.getNameIndex() == ni) {
              return getFieldRefForNameAndType(ctab, j);
            }
          }
        }
        MLog.putMsg(MessageLog.LEVEL_PERROR,
                    "Couldn't find field's Name in constant pool.");
        return -1;
      }
    }
    return -1;
  }


  /**
   * Returns the index in the given constant table which contains the field
   * reference that points to the given name and type reference.
   *
   * @param ctab the constant table to retrieve the information from
   * @param nameAndType the index of the name and type specification in the
   *   constant table
   * @return the index of the field reference object or -1 in case there
   *   is no object with the given name and type specification
   */
  private int getFieldRefForNameAndType(final Constant[] ctab,
                                        final int nameAndType) {
    for (int k = 0; k  <  ctab.length; k++) {
      if (ctab[k] instanceof ConstantFieldref) {
        final ConstantFieldref cfr = (ConstantFieldref) ctab[k];
        if (cfr.getClassIndex() == 1 &&
            cfr.getNameAndTypeIndex() == nameAndType) {
          return k;
        }
      }
    }
    MLog.putMsg(MessageLog.LEVEL_PERROR,
                "Couldn't find FirldRef in constant pool.");
    return -1;
  }

  /**
   * Removes the particular annotation from the class.
   *
   *  @param accessflags the access flags of the invariant to be removed
   */
  public void remove(final int accessflags) {
    this.invariants.remove(Integer.valueOf(accessflags));
  }


  /**
   * Gives all attributes of type matching given bitmask.
   *
   * @param types - set of types (bitmask), from AType
   *     interface.
   * @return array of BML annotations of type matching
   *     given bitmask (it's_type & types  >  0),
   *     ordered by their occurences in string
   *     representation of bytecode.
   */
  public BCPrintableAttribute[] getAllAttributes(final int types) {
    final Vector < BCPrintableAttribute >  v =
      new Vector < BCPrintableAttribute > ();
    if ((types & AType.C_CLASSINVARIANT)  >  0) {
      for (final Enumeration i = this.invariants.elements(); i
          .hasMoreElements();) {
        final ClassInvariant inv = (ClassInvariant) i.nextElement();
        v.add(inv);
      }
    }
    for (int i = 0; i  <  this.methods.length; i++) {
      final BCMethod m = this.methods[i];
      if ((types & AType.C_METHODSPEC)  >  0) {
        if (m.getMspec() != null) {
          v.add(m.getMspec());
        }
      }
      if (m.getAmap() != null) {
        final InCodeAttribute[] at = m.getAmap().getAllAttributes(types);
        for (int j = 0; j  <  at.length; j++) {
          v.add(at[j]);
        }
      }
    }
    final BCPrintableAttribute[] arr = new BCPrintableAttribute[v.size()];
    v.copyInto(arr);
    return arr;
  }


  /**
   * Updates it's JavaClass by writing all BML attributes
   * into it.
   */
  public void saveJC() {
    this.cp.reset();
    final Method[] marr = new Method[this.methods.length];
    for (int i = 0; i  <  this.methods.length; i++) {
      marr[i] = this.methods[i].save();
    }
    this.jc.setMethods(marr);
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "  saving class attributes");
    final AttributeWriter aw = new AttributeWriter(this);
    Attribute[] attrs = removeBMLAttributes(this.jc.getAttributes());
    this.jc.setAttributes(attrs);
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "  saving second constant pool");
    attrs = this.jc.getAttributes();
    for (final Enumeration i = this.invariants.elements();
         i.hasMoreElements();) {
      final ClassInvariant inv = (ClassInvariant) i.nextElement();
      attrs = addAttribute(attrs, aw.writeAttribute(inv));
    }
    this.jc.setAttributes(attrs);
    updateFieldAttributes();
    this.cp.save(this.jc);
  }


  private void updateFieldAttributes() {
    Field[] fields = jc.getFields();
    for (int i = 0; i < fields.length; i++) {
      AttributeWriter aw = new AttributeWriter(this);
      Attribute[] attrs = removeBMLAttributes(fields[i].getAttributes());
      Attribute[] attrsa = new Attribute[attrs.length + 1];
      System.arraycopy(attrs, 0, attrsa, 0, attrs.length);
      attrsa[attrs.length] = aw.writeAttribute(bml_fmodifiers[i].getAttribute());
      fields[i].setAttributes(attrsa);
    }
  }

  /**
   * @param suffix - tree walk order (prefix order for false
   *     and suffix order for true).
   * @return all subexpression (recursively, in prefix order)
   *     from all attributes.
   */
  public BCExpression[] getAllExpressions(final boolean suffix) {
    final BCPrintableAttribute[] all = getAllAttributes();
    final Vector < BCExpression >  expr = new Vector < BCExpression > ();
    for (int i = 0; i  <  all.length; i++) {
      final BCExpression[] e = all[i].getAllExpressions();
      for (int j = 0; j  <  e.length; j++) {
        final BCExpression[] e2 = e[j].getAllNodes(suffix);
        for (int k = 0; k  <  e2.length; k++) {
          expr.add(e2[k]);
        }
      }
    }
    final BCExpression[] exprArr = new BCExpression[expr.size()];
    expr.toArray(exprArr);
    return exprArr;
  }


  /**
   * @return array of all BML annotations, ordered by their
   *     occurrences in string representation of bytecode.
   */
  public BCPrintableAttribute[] getAllAttributes() {
    return getAllAttributes(AType.C_ALL);
  }

  /**
   * Iterates trough each root expression's tree
   * in this class.
   *
   * @param suffix - processing order (true == >  suffix
   *     order, false == >  prefix order),
   * @param ew - visitor (function that will be applied
   *     to each node of the expression's tree).
   * @return given ExrpessionWalker (<code>ew</code>).
   */
  public ExpressionWalker iterate(final boolean suffix,
                                  final ExpressionWalker ew) {
    final BCPrintableAttribute[] all = getAllAttributes();
    for (int i = 0; i  <  all.length; i++) {
      final BCExpression[] e = all[i].getAllExpressions();
      for (int j = 0; j  <  e.length; j++) {
        e[j].iterate(suffix, ew);
      }
    }
    return ew;
  }

  /**
   * Updates it's JavaClass and saves it to file.
   *
   * @param fileName - path to file to save to (in universal representation)
   * @throws IOException - if file cannot be written.
   */
  public void saveToFile(final String fileName) throws IOException {
    final String osSpecificFileName = FileUtils.toOsSpecificName(fileName);
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "saving to: " + fileName);
    saveJC();
    this.jc.dump(osSpecificFileName);
  }
}
