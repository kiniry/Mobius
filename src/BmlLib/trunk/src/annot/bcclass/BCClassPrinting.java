/*
 * @title       "Umbra"
 * @description "An editor for the Java bytecode and BML specifications"
 * @copyright   "(c) 2006-2008 University of Warsaw"
 * @license     "All rights reserved. This program and the accompanying
 *               materials are made available under the terms of the LGPL
 *               licence see LICENCE.txt file"
 */
package annot.bcclass;

import java.util.Enumeration;

import org.apache.bcel.classfile.Field;
import org.apache.bcel.classfile.Utility;

import annot.attributes.ClassInvariant;
import annot.modifiers.BMLModifier;
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
    code.append("\n");
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
    printUpperSection(conf, code, true);
    printUpperSection(conf, code, false);
    printConstructors(conf, code);
    printMethods(conf, code);
    for (final Enumeration i = getInvariantEnum(); i.hasMoreElements();) {
      final ClassInvariant inv = (ClassInvariant) i.nextElement();
      code.append(inv.printCode(conf));
    }
    return conf.getPrettyPrinter().afterDisplay(code.toString());
  }

  /**
   * The method prints out the representation of all the non-constructor
   * methods. The methods are printed out using the grammar:
   *
   *   method ::= [ methodspec ] methodheader [ methodbody ]
   *
   * from "BML Reference Manual" section "Class Member Declarations".
   *
   * @param conf the pretty printing configuration
   * @param code the buffer to print the representation to
   */
  private void printMethods(final BMLConfig conf, final StringBuffer code) {
    for (int i = 0; i  <  getMethodCount(); i++) {
      code.append("\n");
      final BCMethod m = getMethod(i);
      if (!m.isConstructor()) {
        code.append(m.printCode(conf));
      }
    }
  }

  /**
   * The method prints out the representation of all the constructors.
   * The constructors are printed out using the grammar:
   *
   *   method ::= [ methodspec ] methodheader [ methodbody ]
   *
   * from "BML Reference Manual" section "Class Member Declarations".
   *
   * @param conf the pretty printing configuration
   * @param code the buffer to print the representation to
   */
  private void printConstructors(final BMLConfig conf,
                                 final StringBuffer code) {
    for (int i = 0; i  <  getMethodCount(); i++) {
      code.append("\n");
      final BCMethod m = getMethod(i);
      if (m.isConstructor()) {
        code.append(m.printCode(conf));
      }
    }
  }


  /**
   * The method prints out the representation of the specifications.
   * The specifications are printed out using the grammar:
   *
   *   staticspec ::= [ staticinvariants ] [ staticconstraints ]
   *                  [ staticrepresents ] [ staticinitially ]
   * or the grammar
   *
   *   objectspec ::= [ objectinvariants ] [ objectconstraints ]
   *                  [ objectrepresents ] [ objectinitially ]
   *
   * from "BML Reference Manual" section "Textual Representation of
   * Specifications". The choice depends on the flag isStatic. If the
   * flag is <code>true</code> then the static version is generated
   * otherwise the object one.
   *
   * @param conf the pretty printing configuration
   * @param code the buffer to print the representation to
   * @param isStatic the flag which indicates which part should be printed out
   */
  private void printSpecs(final BMLConfig conf,
                          final StringBuffer code,
                          final boolean isStatic) {
    printInvariants(conf, code, isStatic);
    // currently there is no representation for constraints, represents and
    // initially
  }


  /**
   * The method prints out the representation of the invariants.
   * The invariants are printed out using the grammar:
   *
   *   staticinvariants ::= [ static invariant nl ]...
   *
   * or the grammar
   *
   *   objectinvariants ::= [ invariant nl ]...
   *
   * from "BML Reference Manual" section "Textual Representation of
   * Specifications". The choice depends on the flag isStatic. If the
   * flag is <code>true</code> then the static version is generated
   * otherwise the object one.
   *
   * @param conf the pretty printing configuration
   * @param code the buffer to print the representation to
   * @param isStatic the flag which indicates which part should be printed out
   */
  private void printInvariants(final BMLConfig conf,
                               final StringBuffer code,
                               final boolean isStatic) {
    final Enumeration e = getInvariantEnum();
    while (e.hasMoreElements()) {
      final ClassInvariant inv = (ClassInvariant)e.nextElement();
      if (isStatic != inv.isInstance()) {
        code.append(inv.printCode(conf));
      }
    }
  }

  /**
   * The method prints out the representation of the fields.
   * The fields are printed out using the grammar:
   *
   *   staticfields ::= [ staticfield ]...
   *   staticfield ::= static field
   *   field ::= [ nsfieldmodifiers ] type ident ;
   *
   * or the grammar
   *
   *   objectfields ::= [ objectfield ]...
   *   objectfield ::= field
   *   field ::= [ nsfieldmodifiers ] type ident ;
   *
   * from "BML Reference Manual" section "Textual Representation of
   * Specifications". The choice depends on the flag isStatic. If the
   * flag is <code>true</code> then the static version is generated
   * otherwise the object one.
   *
   * Moreover, the methods prints out the Java fields first, then the
   * ghost fields and then the model fields.
   *
   * @param conf the pretty printing configuration
   * @param code the buffer to print the representation to
   * @param isStatic the flag which indicates which part should be printed out
   */
  private void printFields(final BMLConfig conf, final StringBuffer code,
                           final boolean isStatic) {
    printJavaFields(conf, code, isStatic);
    printNonJavaFields(conf, code, isStatic, getGhostFields());
    printNonJavaFields(conf, code, isStatic, getModelFields());
  }

  /**
   * This method prints out the non-Java fields using the grammar mentioned in
   * {@link #printFields(BMLConfig, StringBuffer, boolean)}.
   *
   * @param conf the pretty printing configuration
   * @param code the buffer to print the representation to
   * @param isStatic the flag which indicates which part should be printed out
   * @param fds the array of non-Java fields
   */
  private void printNonJavaFields(final BMLConfig conf,
                                  final StringBuffer code,
                                  final boolean isStatic,
                                  final BCField[] fds) {
    if (fds != null) {
      final StringBuffer res = new StringBuffer("");
      for (int i = 0; i < fds.length; i++) {
        final BCField fd = fds[i];
        if (fd.isStatic() == isStatic) {
          final int af = fd.getAccessFlags();
          res.append(Utility.accessToString(af));
          if (res.length() != 0) res.append(" ");
          res.append(BMLModifier.printBMLModifiers(fd.getBMLFlags()));
          if (res.length() != 0) res.append(" ");
          res.append(fd.getType().toString());
          res.append(" ");
          res.append(fd.getName());
          res.append(";\n");
        }
      }
      code.append(res);
    }
  }


  /**
   * This method prints out the Java fields using the grammar mentioned in
   * {@link #printFields(BMLConfig, StringBuffer, boolean)}.
   *
   * @param conf the pretty printing configuration
   * @param code the buffer to print the representation to
   * @param isStatic the flag which indicates which part should be printed out
   */
  private void printJavaFields(final BMLConfig conf,
                               final StringBuffer code,
                               final boolean isStatic) {
    final Field[] fds = getJC().getFields();
    final StringBuffer res = new StringBuffer("");
    for (int i = 0; i < fds.length; i++) {
      final Field fd = fds[i];
      if (fd.isStatic() == isStatic) {
        final int af = fd.getModifiers();
        res.append(Utility.accessToString(af));
        if (res.length() != 0) res.append(" ");
        res.append(getModifiersForField(i).toString());
        if (res.length() != 0) res.append(" ");
        res.append(fd.getType().toString());
        res.append(" ");
        res.append(fd.getName());
        res.append(";\n");
      }
    }
    code.append(res);
  }


  /**
   * The method prints out the representation of the static section of the
   * class. It uses the grammar:
   *
   *   staticsection ::= [ staticfields ] [ staticspec ]
   *
   * or
   *
   *   objectsection ::= [ objectfields ] [ objectspec ]
   *
   * from "BML Reference Manual" section "Textual Representation of
   * Specifications". The choice depends on the flag isStatic. If the
   * flag is <code>true</code> then the static version is generated
   * otherwise the object one.
   *
   * @param conf the pretty printing configuration
   * @param code the buffer to print the representation to
   * @param isStatic the flag which indicates which part should be printed out
   */
  private void printUpperSection(final BMLConfig conf,
                                 final StringBuffer code,
                                 final boolean isStatic) {
    printFields(conf, code, isStatic);
    printSpecs(conf, code, isStatic);
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
