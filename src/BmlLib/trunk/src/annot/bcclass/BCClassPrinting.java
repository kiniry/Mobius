package annot.bcclass;

import java.util.Enumeration;

import annot.attributes.ClassInvariant;
import annot.textio.BMLConfig;
import annot.textio.DisplayStyle;

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
   *    fileheader ::= packageinfo constant-pools
   *    typeheader ::= class ident [class-extends-clause] [implements-clause]
   *    class-extends-clause ::= extends name
   *    implements-clause ::= implements name-list
   *    name-list ::= name [, name ]...
   *
   * @return String representation of class header.
   */
  @Override
  public String toString() {
    // fileheader
    String ret = printFileHeader();
    // typeheader
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
   *    fileheader ::= packageinfo constant-pools
   * where
   *    packageinfo ::= package packagename nl [ nl ]...
   *    packagename ::= [default] | typename
   *    constant-pools ::= constant-pool [ second-constant-pool ] nl
   *
   * @return String representation of class header.
   */
  public String printFileHeader() {
    final StringBuffer ret = generatePackageInfo();
    ret.append("\n\n");
    MLog.putMsg(MessageLog.LEVEL_PPROGRESS, "displaying constant pool");
    getCp().printCode(ret);
    return ret.append("\n").toString();
  }

  /**
   * Displays a file header, similar to one in Java.
   * This uses the format of the grammar from "BML Reference Manual" section
   * "Textual Representation of Specifications":
   *    packageinfo ::= package packagename
   * where
   *    packagename ::= [default] | typename
   *
   * @return the buffer with the representation of package information
   */
  private StringBuffer generatePackageInfo() {
    String pname = getJC().getPackageName();
    if ("".equals(pname)) {
      pname = DisplayStyle.DEFAULT_PACKAGE_NAME_KWD;
    }
    final StringBuffer ret = new StringBuffer(DisplayStyle.PACKAGE_KWD + " ");
    ret.append(pname);
    return ret;
  }

}
