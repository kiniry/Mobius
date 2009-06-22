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
import java.util.Enumeration;
import java.util.Iterator;
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
import org.apache.bcel.generic.ClassGen;
import org.apache.bcel.generic.ConstantPoolGen;

import annot.attributes.AType;
import annot.attributes.AttributeNames;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.IBCAttribute;
import annot.attributes.clazz.ClassAttribute;
import annot.attributes.clazz.ClassInvariant;
import annot.attributes.clazz.GhostFieldsAttribute;
import annot.attributes.clazz.InvariantsAttribute;
import annot.attributes.field.BMLModifierAttribute;
import annot.attributes.method.InCodeAnnotation;
import annot.bcexpression.BCExpression;
import annot.bcexpression.FieldRef;
import annot.bcexpression.util.ExpressionWalker;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLParser.second_constant_pool_return;
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
   * BML invariants.
   */
  private InvariantsAttribute invariants;

  /**
   * BCEL's {@link ClassGen} for this class, for bytecode
   * operations.
   */
  private ClassGen jc;

  /**
   * Array with methods.
   */
  private BCMethod[] methods;

  /**
   * The BML modifiers for non-BML fields in the class.
   */
  private Vector < BMLModifierAttribute > bml_fmodifiers;

  /**
   * The ghost fields of the class.
   */
  private GhostFieldsAttribute ghostFields;

  /**
   * The model fields of the class.
   */
  private GhostFieldsAttribute modelFields;

  /**
   * A cached package name of the current class.
   */
  private String package_name;

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
        if (AttributeNames.isBMLAttributeName(aname)) {
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
  public boolean addAttribute(final ClassAttribute pa) {
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "adding class attribute: " +
                pa.toString());
    if (pa instanceof InvariantsAttribute) {
      final InvariantsAttribute inv = (InvariantsAttribute) pa;
      this.invariants = inv;
      return true;
    }
    return false;
  }


  /**
   * Adds a Java field to the current class. The field must be
   * created with the constant pool of the current JavaClass.
   *
   * @param f - field to be added
   * @throws ReadAttributeException - if the structure of the attribute
   *   is found not to be correct
   */
  public void addField(final Field f) throws ReadAttributeException {
    getJC().addField(f);
    bml_fmodifiers.add(getJC().getFields().length - 1, getFreshFieldMod(f));
  }

  /**
   * The method adds to the class representation a ghost field. It assumes
   * that the current constant pool contains the information necessary
   * for the field to consistently exist within the class.
   *
   * @param afield the field to add to the class
   */
  public void addGhostField(final BCField afield) {
    ghostFields.add(afield);
  }

  /**
   * Returns the enumerator over all the invariants.
   *
   * @return class invariant enumerator or <code>null</code> in case the
   *   invariants collection does not exist
   */
  public Enumeration getInvariantEnum() {
    if (invariants == null) {
      return null;
    } else {
      return this.invariants.elements();
    }
  }

  /**
   * Adds class invariant to the class at the given position.
   *
   * @param inv - new class invariant.
   * @param pos - the sequence number at which the invariant should be added
   */
  public void setInvariant(final ClassInvariant inv, final int pos) {
    this.invariants.add(inv, pos);
  }


  /**
   * Adds class invariant at the final position of the invariant table.
   *
   * @param inv - new class invariant.
   */
  public void setInvariant(final ClassInvariant inv) {
    this.invariants.add(inv, invariants.size());
  }

  /**
   * Sets the invariants table for this class.
   *
   * @param invs - new class invariant.
   */
  public void setInvariants(final InvariantsAttribute invs) {
    this.invariants = invs;
  }

  /**
   * @return BCEL's {@link ClassGen}
   */
  public ClassGen getBCELClass() {
    return this.getJC();
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
   * Initialize BCClass and read BML attributes from the
   * given JavaClass.
   *
   * @param ajc - {@link ClassGen} to initialize from.
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  protected void load(final ClassGen ajc) throws ReadAttributeException {
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "initializing bcclass");
    this.jc = ajc;
    this.cp = new BCConstantPool(ajc, this);

    MLog.putMsg(MessageLog.LEVEL_PINFO, "  loading class attributes");
    final Attribute[] attrs = ajc.getAttributes();
    final AttributeReader ar = getFreshAttributeReader();
    //it is essential to read the second constant pool first
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        final Unknown attr = (Unknown) attrs[i];
        if (!attr.getName().equals(AttributeNames.SECOND_CONSTANT_POOL_ATTR)) {
          continue;
        }
        ar.readAttribute(attr);
        break;
      }
    }
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        final Unknown attr = (Unknown) attrs[i];
        if (attr.getName().equals(AttributeNames.SECOND_CONSTANT_POOL_ATTR)) {
          continue;
        }
        ar.readAttribute(attr);
      }
    }
    //updateConstantPoolForFields(ghostFields);
    //updateConstantPoolForFields(modelFields);

    final Field[] fields = ajc.getFields();
    this.bml_fmodifiers = new Vector < BMLModifierAttribute > (fields.length);
    for (int i = 0; i  <  fields.length; i++) {
      this.bml_fmodifiers.add(i, getFreshFieldMod(fields[i]));
    }

    final Method[] mtab = ajc.getMethods();
    this.methods = new BCMethod[mtab.length];
    for (int i = 0; i  <  mtab.length; i++) {
      this.methods[i] = getFreshMethod(mtab[i], ajc.getClassName());
    }
  }

  /**
   * This method updates the constant pools in the given fields attribute.
   *
   * @param fields the attribute to update constant pool in
   */
  private void updateConstantPoolForFields(final GhostFieldsAttribute fields) {
    if (fields == null) return;
    final ConstantPool ccp = getCp().getCoombinedCP().getFinalConstantPool();
    for (final Iterator < BCField > i = fields.iterator(); i.hasNext();) {
      final BCField fd = i.next();
      fd.setConstantPool(ccp);
    }
  }

  /**
   * This method generates a fresh BML modifier object for the given field.
   * In case the field contains BML modifiers in its attributes the
   * returned attribute includes the information from the attributes.
   *
   * @param field the field to generate the modifier for
   * @return a fresh modifiers structure for the field
   * @throws ReadAttributeException - if the structure of one of the field
   *   attributes is found not to be correct
   */
  protected abstract BMLModifierAttribute getFreshFieldMod(final Field field)
    throws ReadAttributeException;

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
                                             final String clname)
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
    final Field[] ftab = this.getJC().getFields();
    for (int i = 0; i  <  ftab.length; i++) {
      if (fieldName.equals(ftab[i].getName())) {
        final int ni = ftab[i].getNameIndex();
        final ConstantPoolGen cpg = this.getJC().getConstantPool();
        for (int j = 0; j  <  cpg.getSize(); j++) {
          final Constant cnst = cpg.getConstant(j); 
          if (cnst instanceof ConstantNameAndType) {
            final ConstantNameAndType cnt = (ConstantNameAndType) cnst;
            if (cnt.getNameIndex() == ni) {
              return getFieldRefForNameAndType(cpg, j);
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
   * @param cpg the constant table to retrieve the information from
   * @param nameAndType the index of the name and type specification in the
   *   constant table
   * @return the index of the field reference object or -1 in case there
   *   is no object with the given name and type specification
   */
  private int getFieldRefForNameAndType(final ConstantPoolGen cpg,
                                        final int nameAndType) {
    for (int k = 0; k  <  cpg.getSize(); k++) {
      final Constant cnst = cpg.getConstant(k);
      if (cnst instanceof ConstantFieldref) {
        final ConstantFieldref cfr = (ConstantFieldref) cnst;
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
   * Removes the particular class invariant from the class.
   *
   *  @param classInvariant the invariant to be removed
   */
  public void remove(final ClassInvariant classInvariant) {
    this.invariants.remove(classInvariant);
  }

  /**
   * Removes the whole invariant table from the class.
   */
  public void removeInvariants() {
    invariants = null;
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
        final InCodeAnnotation[] at = m.getAmap().getAllAttributes(types);
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
   * Generates a {@link JavaClass} from the local representation and writes all
   * BML attributes into it.
   */
  public JavaClass saveJC() {
    final JavaClass ajc = this.getJC().getJavaClass();
    final Method[] marr = generateMethodsToSave();
    ajc.setMethods(marr);
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "  saving class attributes");
    final AttributeWriter aw = new AttributeWriter(this);
    Attribute[] attrs = removeBMLAttributes(this.getJC().getAttributes());
    ajc.setAttributes(attrs);
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "   saving second constant pool");
    attrs = ajc.getAttributes();
    attrs = addAndSaveInvariants(aw, attrs);
    attrs = addAndSaveNonJavaFields(aw, attrs, getGhostFields());
    attrs = addAndSaveNonJavaFields(aw, attrs, getModelFields());
    ajc.setAttributes(attrs);
    updateFieldAttributes(ajc);
    this.cp.save(ajc);
    return ajc;
  }

  /**
   * Generates an array of methods which will be saved to the new JavaClass.
   *
   * @return the generated methods
   */
  private Method[] generateMethodsToSave() {
    final Method[] marr = new Method[this.methods.length];
    for (int i = 0; i  <  this.methods.length; i++) {
      marr[i] = this.methods[i].save();
    }
    return marr;
  }

  /**
   * This method extends the given array of attributes and adds to it the
   * attribute with BML fields. In addition, it writes the attribute to the
   * given attribute writer. This method can be used to write both
   * ghost and model fields.
   *
   * @param aw the attribute writer to write the attribute to
   * @param attrs the array of attributes to extend
   * @param ghstFldsAttr the attribute with ghost fields
   * @return the extended array of atributes
   */
  private Attribute[] addAndSaveNonJavaFields(final AttributeWriter aw,
                                     final Attribute[] attrs,
                                     final GhostFieldsAttribute ghstFldsAttr) {
    Attribute[] res = attrs;
    if (ghstFldsAttr.size() > 0) {
      res = addAttribute(res, aw.writeAttribute(ghstFldsAttr));
    }
    return res;
  }

  /**
   * This method adds the attributes from the local representation
   * to the given array of attributes and at the same time it
   * writes the attribute to the given attribute writer.
   *
   * @param aw the writer to write the attributes to
   * @param attrs the array attributes to add the local attributes to
   * @return the original array <code>attrs</code> enriched with the
   *   local invariants
   */
  private Attribute[] addAndSaveInvariants(final AttributeWriter aw,
                                           final Attribute[] attrs) {
    Attribute[] res = attrs;
    res = addAttribute(res, aw.writeAttribute(invariants));
    return res;
  }


  /**
   * This method updates the BML attributes associated with Java fields
   * of the given class.
   * @param ajc the Java class to update fields in
   */
  private void updateFieldAttributes(final JavaClass ajc) {
    final Field[] fields = ajc.getFields();
    for (int i = 0; i < fields.length; i++) {
      final AttributeWriter aw = new AttributeWriter(this);
      final Attribute[] attrs =
        removeBMLAttributes(fields[i].getAttributes());
      Attribute[] attrsa = attrs;
      if (bml_fmodifiers.get(i).getModifiers() != BMLModifiersFlags.BML_NONE) {
        attrsa = new Attribute[attrs.length + 1];
        System.arraycopy(attrs, 0, attrsa, 0, attrs.length);
        attrsa[attrs.length] =
          aw.writeAttribute(bml_fmodifiers.get(i));
      }
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
    JavaClass ajc = saveJC();
    ajc.dump(osSpecificFileName);
  }

  /**
   * Returns the ghost fields in the class.
   *
   * @return the ghost fields of the class
   */
  public GhostFieldsAttribute getGhostFields() {
    if (ghostFields == null) {
      ghostFields = getFreshGhostFields();
    }
    return ghostFields;
  }

  /**
   * Returns an attribute that is supposed to contain ghost fields and which
   * actually contains no fields.
   *
   * @return the ghost fields attribute with no ghost fields
   */
  protected abstract GhostFieldsAttribute getFreshGhostFields();

  /**
   * Returns the model fields in the class.
   *
   * @return the model fields of the class
   */
  public GhostFieldsAttribute getModelFields() {
    if (modelFields == null) {
      modelFields = getFreshGhostFields();
    }
    return modelFields;
  }

  /**
   * Returns the table of the invariants.
   *
   * @return the table of the invariants.
   */
  public IBCAttribute getInvariantTable() {
    if (invariants == null)
      invariants = new InvariantsAttribute((BCClass) this);
    return invariants;
  }

  /**
   * Returns the BML modifier for the field of the given number.
   *
   * @param i the number of the field (as in the fields array in the
   *   local representation
   * @return the modifier for the given field
   */
  public BMLModifierAttribute getBMLModifierForField(final int i) {
    try {
      return bml_fmodifiers.get(i);
    } catch (ArrayIndexOutOfBoundsException e) {
      return null;
    }
  }


  /**
   * Removes all the ghost fields from the class.
   */
  public void removeGhostFields() {
    this.ghostFields = getFreshGhostFields();
  }

  /**
   * Sets the ghost fields to the object given as the argument. It assumes the
   * constant pool is up to date.
   *
   * @param gfa the attribute with the ghost fields
   */
  public void setGhostFields(final GhostFieldsAttribute gfa) {
    ghostFields = gfa;
  }
  

  public String getPackageName() {
    if (package_name == null) {
      String cname = getBCELClass().getClassName();
      int index = cname.lastIndexOf('.');
      if(index < 0)
        package_name = "";
      else
        package_name = cname.substring(0, index);
    }
    return package_name;
  }


  public ClassGen getJC() {
    return jc;
  }
}
