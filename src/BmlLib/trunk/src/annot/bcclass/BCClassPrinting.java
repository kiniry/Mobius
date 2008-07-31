package annot.bcclass;

import java.util.Enumeration;

import org.apache.bcel.Constants;
import org.apache.bcel.classfile.Constant;
import org.apache.bcel.classfile.ConstantClass;
import org.apache.bcel.classfile.ConstantUtf8;

import annot.attributes.ClassInvariant;
import annot.textio.BMLConfig;

/**
 * This class handles the pretty printing of the BMLLib class. It extends the
 * BML class representation with this functionality.
 *
 * @author Tomasz Batkiewicz (tb209231@students.mimuw.edu.pl)
 * @author Aleksy Schubert (alx@mimuw.edu.pl)
 * @version a-01
 */
public abstract class BCClassPrinting extends BCClassRepresentation {

  /**
   * Dumps all string representation of the current class, with BML annotations.
   * This uses the format of the grammar from "BML Reference Manual" section
   * "Textual Representation of Specifications":
   *
   *    classfile ::= fileheader typeheader typebody
   *
   * @return string representation of the bytecode in the current class
   */
  public String printCode() {
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS,
                "generating string repr. of the class");
    final BMLConfig conf = new BMLConfig();
    //fileheader typeheader
    final StringBuffer code = new StringBuffer(toString());
    //typebody
    return conf.getPrettyPrinter().afterDisplay(
      code.append(printTypeBody(conf)).toString());
  }


  /**
   * Dumps the string representation of the current type body, with BML
   * annotations. This uses the format of the grammar from
   * "BML Reference Manual" section "Textual Representation of Specifications":
   *
   *    typebody ::= [ staticsection ] [ objectsection ] constructor [ methods ]
   *
   * @param conf the configuration of the display on which the returned string
   *   is printed out
   * @return string representation of the bytecode in the current class
   */
  public String printTypeBody(final BMLConfig conf) {
    final StringBuffer code = new StringBuffer("");
    for (final Enumeration i = getInvariantEnum(); i.hasMoreElements();) {
      final ClassInvariant inv = (ClassInvariant) i.nextElement();
      code.append(inv.printCode(conf));
    }
    for (int i = 0; i  <  getMethodCount(); i++) {
      code.append("\n");
      code.append(getMethod(i).printCode(conf));
    }
    return conf.getPrettyPrinter().afterDisplay(code.toString());
  }


  /**
   * Displays class file header, similar to one in Java.
   * This uses the format of the grammar from "BML Reference Manual" section
   * "Textual Representation of Specifications":
   *    fileheader typeheader
   * where
   *    fileheader ::= packageinfo [ imports ]
   *    typeheader ::= class ident [class-extends-clause] [implements-clause]
   *    class-extends-clause ::= extends name
   *    implements-clause ::= implements name-list
   *    name-list ::= name [, name ]...
   *
   * @return String representation of class header.
   */
  @Override
  public String toString() {
    String ret = printFileHeader();
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
    ret += "class " + getJC().getClassName();
    if (!"java.lang.Object".equals(getJC().getSuperclassName())) {
      ret += " extends " + getJC().getSuperclassName();
    }
    final String[] interfaceNames = getJC().getInterfaceNames();
    if (interfaceNames.length  >  0) {
      ret += " implements ";
      for (int i = 0; i  <  interfaceNames.length; i++) {
        ret += interfaceNames[i] + (i  <  interfaceNames.length - 1 ?
                                   ", " : "");
      }
    }
    return ret + "\n";
  }

  /**
   * Displays a file header, similar to one in Java.
   * This uses the format of the grammar from "BML Reference Manual" section
   * "Textual Representation of Specifications":
   *    fileheader ::= packageinfo [ imports ]
   * where
   *
   * @return String representation of class header.
   */
  public String printFileHeader() {
    String pname = getJC().getPackageName();
    if ("".equals(pname)) {
      pname = "[default]";
    }
    final StringBuffer ret = new StringBuffer("package ");
    ret.append(pname);
    ret.append("\n\n");
    for (int i = 0; i < getCp().size(); i++) {
      final Constant constant = getCp().getConstant(i);
      if (constant != null && constant.getTag() == Constants.CONSTANT_Class) {
        final int namenum = ((ConstantClass)constant).getNameIndex();
        if (getJC().getClassNameIndex() != i) {
          final String name = ((ConstantUtf8)getCp().getConstant(namenum)).
            getBytes();
          ret.append("import ").append(name).append("\n");
        }
      }
    }
    return ret.append("\n").toString();
  }


  /**
   * Displays constant pools.
   *
   * @return String representation of class' constant pool,
   *     including second constant pool, if any.
   */
  public String printCp() {
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "displaying constant pool");
    return getCp().printCode();
  }

}
