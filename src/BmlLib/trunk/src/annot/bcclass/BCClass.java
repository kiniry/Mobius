package annot.bcclass;

import java.io.IOException;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import org.apache.bcel.classfile.Attribute;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantFieldref;
import org.apache.bcel.classfile.ConstantNameAndType;
import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.JavaClass;
import org.apache.bcel.classfile.Method;
import org.apache.bcel.classfile.Unknown;
import org.apache.bcel.generic.ConstantPoolGen;
import org.apache.bcel.generic.MethodGen;
import org.apache.bcel.util.ClassPath;
import org.apache.bcel.util.SyntheticRepository;

import annot.attributes.AType;
import annot.attributes.BCPrintableAttribute;
import annot.attributes.ClassInvariant;
import annot.attributes.InCodeAttribute;
import annot.bcexpression.BCExpression;
import annot.bcexpression.util.ExpressionWalker;
import annot.io.AttributeReader;
import annot.io.AttributeWriter;
import annot.io.ReadAttributeException;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;
import annot.textio.Parsing;

/**
 * This class represents a bytecode class. It should be
 * created at the beginning of using this library
 * (for each bytecode class). This library can be used to
 * manipulate BML annotations, while operation on bytecode
 * itself can be performed using methods from BCEL library,
 * but BCEL's object should be accessed from this class.
 * JavaClass from this object (jc field) should be
 * the same as JavaClass used for performing operations on
 * bytecode using BCEL library. Also all BCEL methods should
 * be accessed (or at least be the same) from this class
 * (getMethod(index).getBCELMethod()).
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public class BCClass {

  /**
   * Constant pool (including second constant pool's
   * constants).
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
   * Method array.
   */
  private BCMethod[] methods;

  /**
   * A set of functions for parsing annotations.
   */
  private Parsing parser;

  /**
   * A constructor from already existing JavaClass. That
   * JavaClass should be used for operations on byte code
   * using the BCEL library.
   *
   * @param jc - JavaClass representing byte code class
   *     this class should operate on.
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  public BCClass(final JavaClass jc) throws ReadAttributeException {
    load(jc);
  }

  /**
   * A constructor from a .class file. It loads JavaClass
   * from that file (using BCEL) first, then loads BML
   * annotations from it. Don't forget to get JavaClass
   * from constructed object (getJC() method), instead of
   * creating a new instance of JavaClass using BCEL.
   *
   * @param dirName - path of directory where .class file
   *     is located, excluding directories included
   *     in <code>className</code>,
   * @param className - package and class name of class that
   *     should be loaded. For example, constructor call:
   *     BCClass("C:\\workspace\\Project\\", "test.aclass");
   *     searches for file:
   *     C:\workspace\Project\test\aclass.class,
   * @throws ClassNotFoundException - iff .class file
   *     could not be found,
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  public BCClass(final String dirName, final String className)
    throws ClassNotFoundException, ReadAttributeException {
    MLog.putMsg(MessageLog.PInfo, "filename=" + dirName);
    MLog.putMsg(MessageLog.PInfo, "className=" + className);
    final ClassPath acp = new ClassPath(dirName);
    SyntheticRepository.getInstance(acp).clear();
    final JavaClass jc = SyntheticRepository.getInstance(acp)
        .loadClass(className);
    load(jc);
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
        final int access_flags1 = catr.getBytes()[0] * 256 + catr.getBytes()[1];
        final int access_flags2 = ua.getBytes()[0] * 256 + ua.getBytes()[1];
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
        if (DisplayStyle.__classInvariant.equals(aname)) {
          continue;
        }
        if (DisplayStyle.__mspec.equals(aname)) {
          continue;
        }
        if (DisplayStyle.__assertTable.equals(aname)) {
          continue;
        }
        if (DisplayStyle.__loopSpecTable.equals(aname)) {
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
   * A method to convert the universal path representation
   * ("/" separates the path segments) to the local operating
   * system specific one.
   *
   * @param fileName the path in the universal representation
   * @return the path in the local operating system representation
   */
  private static String toOsSpecificName(final String fileName) {
    final String filesep = System.getProperty("file.separator");
    return fileName.replaceAll("/", Parsing.escape(filesep));
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
    MLog.putMsg(MessageLog.PProgress, "adding class attribute: " +
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
   * @return array of all BML annotations, ordered by their
   *     occurences in string representation of bytecode.
   */
  public BCPrintableAttribute[] getAllAttributes() {
    return getAllAttributes(AType.C_ALL);
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
   * @return constant pool (from this library, not
   * BCEL's one)
   */
  public BCConstantPool getCp() {
    return this.cp;
  }

  /**
   * Searches constant pool for index of this class'es field
   * of given name.
   *
   * @param fieldName - name of a field in this class.
   * @return field's index, for use in
   *     {@link FieldRef#FieldRef(boolean, BCConstantPool, int)},
   *     <br> or <b>-1</b> if this class has no fields
   *     of given name.
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
              for (int k = 0; k  <  ctab.length; k++) {
                if (ctab[k] instanceof ConstantFieldref) {
                  final ConstantFieldref cfr = (ConstantFieldref) ctab[k];
                  if (cfr.getClassIndex() == 1 &&
                      cfr.getNameAndTypeIndex() == j) {
                    return k;
                  }
                }
              }
              MLog.putMsg(MessageLog.PError,
                          "Couldn't find FirldRef in constant pool.");
              return -1;
            }
          }
        }
        MLog.putMsg(MessageLog.PError,
                    "Couldn't find field's Name in constant pool.");
        return -1;
      }
    }
    return -1;
  }

  /**
   * @return class invariant.
   */
  public ClassInvariant getInvariant(final int accessflags) {
    return (ClassInvariant) this.invariants.get(Integer.valueOf(accessflags));
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
   *     (including  < clinit >  and  < init > , if any).
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
   * @return object used for parsing BML annotations.
   */
  public Parsing getParser() {
    return this.parser;
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
   * Initialize BCClass and read BML attributes from
   * given JavaClass.
   *
   * @param jc - JavaClass to initialize from.
   * @throws ReadAttributeException - if any of BML
   *     attributes wasn't correctly parsed
   *     by this library.
   */
  private void load(final JavaClass jc) throws ReadAttributeException {
    MLog.putMsg(MessageLog.PProgress, "initializing bcclass");
    this.jc = jc;
    this.cp = new BCConstantPool(jc);
    this.parser = new Parsing(this);
    MLog.putMsg(MessageLog.PInfo, "  loading class attributes");
    final Attribute[] attrs = jc.getAttributes();
    final AttributeReader ar = new AttributeReader(this);
    for (int i = 0; i  <  attrs.length; i++) {
      if (attrs[i] instanceof Unknown) {
        ar.readAttribute((Unknown) attrs[i]);
      }
    }
    final Method[] mtab = jc.getMethods();
    this.methods = new BCMethod[mtab.length];
    for (int i = 0; i  <  mtab.length; i++) {
      this.methods[i] = new BCMethod(this, new MethodGen(mtab[i], jc
          .getClassName(), new ConstantPoolGen(jc.getConstantPool())));
    }
  }

  /**
   * Dumps all bytecode of this class, with BML annotations. This uses
   * the format of the grammar from "BML Reference Manual":
   *
   *    classfile ::= fileheader classheader classbody
   *
   * @return string representation of this class' bytecode.
   */
  public String printCode() {
    MLog.putMsg(MessageLog.PProgress, "generating class' code");
    final BMLConfig conf = new BMLConfig();
    final StringBuffer code = new StringBuffer(toString());
    for (final Enumeration i = this.invariants.elements();
         i.hasMoreElements();) {
      final ClassInvariant inv = (ClassInvariant) i.nextElement();
      code.append(inv.printCode(conf));
    }
    for (int i = 0; i  <  this.methods.length; i++) {
      code.append("\n");
      code.append(this.methods[i].printCode(conf));
    }
    return conf.getPrettyPrinter().afterDisplay(code.toString());
  }

  /**
   * Displays constant pools.
   *
   * @return String representation of class' constant pool,
   *     including secons constant pool, if any.
   */
  public String printCp() {
    MLog.putMsg(MessageLog.PProgress, "displaying constant pool");
    return this.cp.printCode();
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
    MLog.putMsg(MessageLog.PProgress, "  saving class attributes");
    final AttributeWriter aw = new AttributeWriter(this);
    Attribute[] attrs = removeBMLAttributes(this.jc.getAttributes());
    this.jc.setAttributes(attrs);
    MLog.putMsg(MessageLog.PProgress, "  saving second constant pool");
    attrs = this.jc.getAttributes();
    for (final Enumeration i = this.invariants.elements();
         i.hasMoreElements();) {
      final ClassInvariant inv = (ClassInvariant) i.nextElement();
      attrs = addAttribute(attrs, aw.writeAttribute(inv));
    }
    this.jc.setAttributes(attrs);
    this.cp.save(this.jc);
  }

  /**
   * Updates it's JavaClass and saves it to file.
   *
   * @param fileName - path to file to save to (in universal representation)
   * @throws IOException - if file cannot be written.
   */
  public void saveToFile(final String fileName) throws IOException {
    final String osSpecificFileName = toOsSpecificName(fileName);
    MLog.putMsg(MessageLog.PProgress, "saving to: " + fileName);
    saveJC();
    this.jc.dump(osSpecificFileName);
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
   * Displays class header, similar to one in Java. It uses the grammar:
   *    fileheader classheader
   * where
   *    fileheader ::= packageinfo [ imports ]
   *    classheader ::= class ident [class-extends-clause] [implements-clause]
   *    class-extends-clause ::= extends name
   *    implements-clause ::= implements name-list
   *    name-list ::= name [, name ]...
   *
   * @return String representation of class header.
   */
  @Override
  public String toString() {
    String pname = this.jc.getPackageName();
    if ("".equals(pname)) {
      pname = "[default]";
    }
    String ret = "package " + pname + "\n\n";
    /*
    if (jc.isPublic())
      ret += "public ";
    if (jc.isPrivate())
      ret += "private ";
    if (jc.isProtected())
      ret += "protected ";
    if (jc.isAbstract())
      ret += "abstract ";
    if (jc.isFinal())
      ret += "final ";
    */
    ret += "class " + this.jc.getClassName();
    if (!"java.lang.Object".equals(this.jc.getSuperclassName())) {
      ret += " extends " + this.jc.getSuperclassName();
    }
    final String[] interfaceNames = this.jc.getInterfaceNames();
    if (interfaceNames.length  >  0) {
      ret += " implements ";
      for (int i = 0; i  <  interfaceNames.length; i++) {
        ret += interfaceNames[i] + (i  <  interfaceNames.length - 1 ?
                                   ", " : "");
      }
    }
    return ret + "\n";
  }
}
