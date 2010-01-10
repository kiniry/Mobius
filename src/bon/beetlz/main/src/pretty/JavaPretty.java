/**
 * Pretty printing or skeleton printing.
 */
package pretty;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.SortedSet;
import java.util.Vector;


import logic.BeetlzExpression;
import logic.BeetlzExpression.Nullity;
import main.Beetlz;

import structure.ClassCollection;
import structure.ClassStructure;
import structure.FeatureStructure;
import structure.Invariant;
import structure.Spec;
import structure.ClassStructure.Comment;
import utils.BConst;
import utils.Helper;
import utils.PrettyFormatter;
import utils.smart.SmartString;

/**
 * Prints pretty printed BON model code.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 * TODO: print AST
 */
public class JavaPretty {
  /** Tab. */
  private final String my_tab;
  /** Newline character. */
  private final String my_newline = "\n"; //$NON-NLS-1$
  /** Semicolon character. */
  private final String my_semicolon = ";"; //$NON-NLS-1$

  /**
   * Create a new pretty printer instance.
   * @param a_tab tab to be used
   */
  public JavaPretty(final String a_tab) {
    my_tab = a_tab;
  }

  /**
   * Print the classcollection to file(s).
   * @param a_dir directory where to place the file(s)
   * @param the_classes classes to pretty print
   */
  public final void printToFiles(final String a_dir, final ClassCollection the_classes) {
    final Map < String , Package > classes = this.createFromClasses(the_classes);
    final File dir = new File(a_dir);
    if (!dir.exists()) {
      Beetlz.JAVA_LOGGER.
        severe(Beetlz.getResourceBundle().
               getString("JavaPretty.directoryDoesNotExist")); //$NON-NLS-1$
      return;
    }
    if (!dir.isDirectory()) {
      Beetlz.JAVA_LOGGER.
        severe(Beetlz.getResourceBundle().
               getString("JavaPretty.directoryIsNotDirectory")); //$NON-NLS-1$
      return;
    }

    if (Beetlz.getProfile().skeletonOneFile()) {
      try {
        final BufferedWriter out =
          new BufferedWriter(new FileWriter(dir + "/" + //$NON-NLS-1$
                                            "beetlzSkeletonCode.txt")); //$NON-NLS-1$

        printClassCollection(the_classes, out);
        out.close();
      } catch (final IOException e) {
        Beetlz.JAVA_LOGGER.
          severe(String.
                 format(Beetlz.getResourceBundle().
                        getString("JavaPretty.errorWritingFile"), //$NON-NLS-1$
                                  dir + "beetlzSkeletonCode.txt")); //$NON-NLS-1$
      }
    //end skeleton file
    } else {
      for (final String packName : classes.keySet()) {
        final File temp = new File(dir + "/" + packName); //$NON-NLS-1$
        boolean dir_ready = true;
        if (!temp.exists()) { //overwrite if exists
          dir_ready = temp.mkdirs();
        }
        if (dir_ready) {
          for (final String clsName : classes.get(packName).my_classes.keySet()) {
            try {
              final BufferedWriter out =
                new BufferedWriter(new FileWriter(dir + "/" +
                                                  packName + "/" + //$NON-NLS-1$ //$NON-NLS-2$
                                                  clsName + ".java")); //$NON-NLS-1$
              out.write(my_newline + my_newline);
              for (final String line : classes.get(packName).my_classes.get(clsName)) {
                out.write(line);
              }
              out.flush();
              out.close();
            } catch (final IOException e) {
              Beetlz.JAVA_LOGGER.
                severe(String.
                       format(Beetlz.getResourceBundle().
                              getString("JavaPretty.errorWritingFile"), //$NON-NLS-1$
                              dir + "/" + //$NON-NLS-1$
                              packName + "/" + clsName)); //$NON-NLS-1$
            }
          }
        }
      }
    }
  }


  /**
   * Print a class collection.
   * @param the_classes classes to print
   * @param the_out writer to print to
   */
  public final void printClassCollection(final ClassCollection the_classes,
                                   final Writer the_out) {
    final Map < String , Package > classes = this.createFromClasses(the_classes);
    try {
      for (final Package p : classes.values()) {
        the_out.write("//***********  package " + //$NON-NLS-1$
                  p.my_name + "  ***********\n\n"); //$NON-NLS-1$
        for (final List < String > cls : p.my_classes.values()) {
          for (final String s : cls) {
            the_out.write(s);
          }
        }

      }
      the_out.flush();
    } catch (final IOException e) {
      e.printStackTrace();
    }

  }

  /**
   * Pretty print classes.
   * @param the_classes to be printed
   * @return map of package name - classes inside it
   */
  public final Map < String , Package > createFromClasses(final ClassCollection the_classes) {
    final Map < String , Package > classes = new HashMap < String , Package > ();
    for (final ClassStructure c : the_classes.getClasses()) {

      if (!c.isPrivate()) { //do not print private classes, impl detail
        final String pack = getInnermostPackage(c);
        if (classes.containsKey(pack)) {
          classes.get(pack).my_classes.
            put(PrettyFormatter.formatJavaClassName(c.getSimpleName()), printClass(c));
        } else {
          final Package p = new Package(pack);
          p.my_classes.put(PrettyFormatter.
                           formatJavaClassName(c.getSimpleName()),
                           printClass(c));
          classes.put(pack, p);
        }
      }
    }
    return classes;

  }

  /**
   * Pretty print one class.
   * @param the_class class to print
   * @return list of lines of this pretty printed class
   */
  private List < String > printClass(final ClassStructure the_class) {
    final List < String > cls = new Vector < String > ();
    cls.addAll(printClassComments(the_class));
    cls.addAll(printClassHeader(the_class));

    if (the_class.hasFeatures()) {
      if (Beetlz.getProfile().pureBon()) {
        cls.addAll(printFeatures(the_class.getConstructors()));
        cls.addAll(printFeatures(the_class.getFeatures()));
      } else {
        cls.addAll(printConstructors(the_class));
        cls.addAll(printFeatures(the_class.getFeatures()));
      }

      if (the_class.isRoot()) {
        cls.add(my_tab + "public void run() {}" + my_newline); //$NON-NLS-1$
      }

    }
    cls.addAll(printInvariant(the_class.getInvariant()));
    cls.add("}" + my_newline + my_newline); //$NON-NLS-1$

    return cls;
  }


  /**
   * Print class header.
   * @param the_class the classes to print
   * @return list of lines
   */
  private List < String > printClassHeader(final ClassStructure the_class) {
    final List < String > classDecl = new Vector < String > ();
    //public protected private
    //abstract static final strictfp
    String header = ""; //$NON-NLS-1$
    if (the_class.isPublic()) header += "public "; //$NON-NLS-1$
    else if (the_class.isProtected()) header += "protected "; //$NON-NLS-1$
    else if (the_class.isPrivate()) header += "private "; //$NON-NLS-1$

    header += "/*@ nullable_by_default @*/ "; //$NON-NLS-1$

    if (the_class.isAbstract()) header += "abstract class "; //$NON-NLS-1$
    else if (the_class.isEnum()) header += "enum "; //$NON-NLS-1$
    else if (Helper.qualifiesAsInterface(the_class)) header += "interface "; //$NON-NLS-1$
    else if (the_class.isRoot()) header += "class "; //$NON-NLS-1$
    else header += "class "; //$NON-NLS-1$

    //class name
    header += PrettyFormatter.
      formatJavaClassName(the_class.getSimpleName()) + " "; //$NON-NLS-1$

    //Generics
    final List < SmartString > gen = the_class.getGenerics();
    if (gen.size() > 0) {
      header += "< "; //$NON-NLS-1$
      for (int i = 0; i < gen.size() - 1; i++) {
        header += PrettyFormatter.getJavaType(gen.get(i)) + ", "; //$NON-NLS-1$
      }
      header += PrettyFormatter.getJavaType(gen.get(gen.size() - 1));
      header += " > "; //$NON-NLS-1$
    }
    //Extends
    final SortedSet < SmartString > interf = the_class.getInterfaces();

    //Implements
    if (the_class.isRoot()) {
      interf.add(new SmartString("Runnable")); //$NON-NLS-1$
    }
    if (the_class.isPersistent()) {
      interf.add(new SmartString("Serializable")); //$NON-NLS-1$
    }
    if (interf.size() > 0) {
      header += "implements "; //$NON-NLS-1$
      final Iterator < SmartString > i = interf.iterator();
      for (int j = 0; j < interf.size() - 1; j++) {
        header += PrettyFormatter.getJavaType(i.next()) + ", "; //$NON-NLS-1$
      }
      header += PrettyFormatter.getJavaType(i.next());
    }
    header += " {" + my_newline; //$NON-NLS-1$
    classDecl.add(header);
    return classDecl;
  }


  /**
   * Print class comments.
   * @param the_class class to print
   * @return list of lines
   */
  private List < String > printClassComments(final ClassStructure the_class) {
    final List < String > comment = new Vector < String > ();
    final Comment comm = the_class.getComments();
    if (!comm.isEmpty()) {
      comment.add("/**" + my_newline); //$NON-NLS-1$
      if (comm.my_about != null && !comm.my_about.isEmpty()) {
        for (int i = 0; i < comm.my_about.size(); i++) {
          comment.add(" * " + comm.my_about.get(i).//$NON-NLS-1$
                      replace("\"", "") + //$NON-NLS-1$ //$NON-NLS-2$
                      my_newline);
        }
      }
      if (comm.my_allElse != null && comm.my_allElse.length() > 0) {
        comment.add(" * " + comm.my_allElse.trim() + my_newline); //$NON-NLS-1$
      }
      if (comm.my_author != null && comm.my_author.length() > 0) {
        comment.add(" * " + BConst.JAVA_AUTHOR + " " +
                    comm.my_author.trim() + my_newline); //$NON-NLS-1$ //$NON-NLS-2$
      }
      if (comm.my_version != null && comm.my_version.length() > 0) {
        comment.add(" * " + BConst.JAVA_VERSION + " " +
                    comm.my_version.trim() + my_newline); //$NON-NLS-1$ //$NON-NLS-2$
      }
      comment.add(" */" + my_newline); //$NON-NLS-1$
    }
    return comment;
  }

  /**
   * Print all constructors.
   * @param the_class class to print
   * @return list of lines
   */
  private List < String > printConstructors(final ClassStructure the_class) {
    final int two = 2;
    final List < String > constructor = new Vector < String > ();
    final List < FeatureStructure > cons =
      new Vector < FeatureStructure > (the_class.getConstructors());
    for (final FeatureStructure f : cons) {
      constructor.addAll(printFeatureSpec(f.getSpec()));
      String head = my_tab;
      if (f.isPublic()) head += "public "; //$NON-NLS-1$
      else if (f.isProtected()) head += "protected "; //$NON-NLS-1$
      else if (f.isPrivate()) head += "private "; //$NON-NLS-1$

      //Pure?
      if (f.isQuery()) {
        head += "/*@ pure @*/ "; //$NON-NLS-1$
      }

      head += PrettyFormatter.
        formatJavaClassName(the_class.getSimpleName()) + "("; //$NON-NLS-1$
      final Map < String, SmartString > params = f.getSignature().getFormalParameter();
      if (params.size() > 0) {
        for (final String s : params.keySet()) {
          if (params.get(s).getNullity() == Nullity.NON_NULL) {
            head += "/*@ non_null @*/ "; //$NON-NLS-1$
          }
          head += PrettyFormatter.getJavaType(params.get(s)) +
            " " + s + ", "; //$NON-NLS-1$ //$NON-NLS-2$
        }
        head = head.substring(0, head.length() - two);
      }

      head += "){}" + my_newline; //$NON-NLS-1$

      constructor.add(head);
    }
    if (cons.size() > 0) {
      constructor.add(my_newline);
    }
    return constructor;
  }

  /**
   * Print all features.
   * @param the_features_to_print list of features
   * @return list if lines
   */

  private List < String > printFeatures
  (final SortedSet < FeatureStructure > the_features_to_print) {
    final List < String > feature = new Vector < String > ();
    final List < FeatureStructure > feat =
      new Vector < FeatureStructure > (the_features_to_print);
    final List < FeatureStructure > variables = new Vector < FeatureStructure > ();
    final List < FeatureStructure > allElse = new Vector < FeatureStructure > ();
    for (final FeatureStructure f : feat) {
      if (f.isQuery() &&
          f.getSignature().getFormalParameter().isEmpty() &&
          !f.getSpec().isEmpty() &&
          f.getSpec().get(0).getPostconditions().isEmpty() &&
          f.getSpec().get(0).getPreconditions().isEmpty()) {
        variables.add(f);
      } else {
        allElse.add(f);
      }
    }

    for (final FeatureStructure f : variables) {
      feature.addAll(printVariable(f));
    }
    for (final FeatureStructure f : allElse) {
      feature.addAll(printFeatureSpec(f.getSpec()));
      feature.addAll(printMethod(f, f.getSimpleName()));
    }

    return feature;
  }

  /**
   * Print a variable.
   * @param the_var variable to print
   * @return list of lines
   */
  private List < String > printVariable(final FeatureStructure the_var) {
    final List < String > variable = new Vector < String > ();
    //public protected private abstract static
    //final synchronized native strictfp
    String head = my_tab;
    if (the_var.isPublic()) head += "public "; //$NON-NLS-1$
    else if (the_var.isProtected()) head += "protected "; //$NON-NLS-1$
    else if (the_var.isPrivate()) head += "private "; //$NON-NLS-1$

    if (the_var.isAbstract()) head += "abstract "; //$NON-NLS-1$
    else if (the_var.isConstant()) head += "final "; //$NON-NLS-1$

    //Return type
    final SmartString returnType = the_var.getSignature().getReturnValue();
    if (returnType.equals(SmartString.getVoid())) {
      head += "void "; //$NON-NLS-1$
    } else {
      if (returnType.getNullity() == Nullity.NON_NULL) {
        head += "/*@ non_null @*/ "; //$NON-NLS-1$
      }
      head += PrettyFormatter.getJavaType(returnType);
    }

    if (the_var.isConstant()) {
      head += " " + the_var.getSimpleName().toUpperCase(); //$NON-NLS-1$
    } else {
      head += " " + the_var.getSimpleName(); //$NON-NLS-1$
    }

    if (the_var.isConstant() &&
        !the_var.getSpec().get(0).getConstantValue().equals(Spec.UNKNOWN_VALUE)) {
      head += " = " + the_var.getSpec().get(0).getConstantValue() +
        ";" + my_newline; //$NON-NLS-1$ //$NON-NLS-2$
    } else {
      head += ";" + my_newline; //$NON-NLS-1$
    }
    variable.add(head);
    return variable;
  }

  /**
   * Print a method.
   * @param the_feature method to print
   * @param the_name name to be used
   * @return list if lines
   */
  private List < String > printMethod(final FeatureStructure the_feature,
                                      final String the_name) {
    final int two = 2;
    final List < String > method = new Vector < String > ();
    //public protected private abstract static
    //final synchronized native strictfp
    String head = my_tab;
    if (the_feature.isPublic()) head += "public "; //$NON-NLS-1$
    else if (the_feature.isProtected()) head += "protected "; //$NON-NLS-1$
    else if (the_feature.isPrivate()) head += "private "; //$NON-NLS-1$

    if (the_feature.isAbstract()) head += "abstract "; //$NON-NLS-1$
    else if (the_feature.isConstant()) head += "final "; //$NON-NLS-1$

    //Pure?
    if (the_feature.isQuery()) {
      head += "/*@ pure @*/ "; //$NON-NLS-1$
    }

    //Return type
    final SmartString returnType = the_feature.getSignature().getReturnValue();
    if (returnType.equals(SmartString.getVoid())) {
      head += "void "; //$NON-NLS-1$
    } else {
      if (returnType.getNullity() == Nullity.NON_NULL) {
        head += "/*@ non_null @*/ "; //$NON-NLS-1$
      }
      head += PrettyFormatter.getJavaType(returnType) + " "; //$NON-NLS-1$
    }

    head += the_name + "("; //$NON-NLS-1$
    final Map < String, SmartString > params = the_feature.getSignature().getFormalParameter();
    if (params.size() > 0) {
      for (final String s : params.keySet()) {
        if (params.get(s).getNullity() == Nullity.NON_NULL) {
          head += "/*@ non_null @*/ "; //$NON-NLS-1$
        }
        head += PrettyFormatter.getJavaType(params.get(s)) +
          " " + s + ", "; //$NON-NLS-1$ //$NON-NLS-2$
      }
      head = head.substring(0, head.length() - two);
    }

    if (the_feature.isAbstract()) head += ");" + my_newline; //$NON-NLS-1$
    else head += "){}" + my_newline; //$NON-NLS-1$
    method.add(head);
    return method;
  }

  /**
   * Print feature specs.
   * @param the_spec_cases list of specs to print
   * @return list of lines
   */
  private List < String > printFeatureSpec(final List < Spec > the_spec_cases) {
    if (the_spec_cases.isEmpty() ||
        Beetlz.getProfile().noJml()) return new Vector < String > ();
    final Spec s = the_spec_cases.get(0);
    final List < String > spec = new Vector < String > ();
    final List < BeetlzExpression > frame = new Vector < BeetlzExpression > (s.getFrame());
    String args = ""; //$NON-NLS-1$
    if (frame.size() > 0) {
      for (int i = 0; i < frame.size() - 1; i++) {
        //args += PrettyFormatter.getJavaFrameName(frame.get(i)) + ", "; //$NON-NLS-1$
        args += frame.get(i).toJavaString();
      }
      //args += PrettyFormatter.getJavaFrameName(frame.get(frame.size() - 1));
      args += frame.get(frame.size() - 1).toJavaString();
    }

    if (!s.isEmpty()) spec.add(my_newline);

    if (!args.equals("\\everything") && !s.isPure()) { //do not print default //$NON-NLS-1$
      spec.add(my_tab + "//@ assignable " + args + my_semicolon + my_newline); //$NON-NLS-1$
    }
    for (final BeetlzExpression e : s.getNonTrivialPreconditions()) {
      spec.add(my_tab + "//@ requires " + e.toJavaString() +
               my_semicolon + my_newline); //$NON-NLS-1$
    }
    for (final BeetlzExpression e : s.getInformalPreconditions()) {
      spec.add(my_tab + "//@ requires (* " + e.toJavaString() +
               " *)" + my_semicolon + my_newline); //$NON-NLS-1$ //$NON-NLS-2$
    }
    for (final BeetlzExpression e : s.getNonTrivialPostconditions()) {
      spec.add(my_tab + "//@ ensures " + e.toJavaString() +
               my_semicolon + my_newline); //$NON-NLS-1$
    }
    for (final BeetlzExpression e : s.getInformalPostconditions()) {
      spec.add(my_tab + "//@ ensures (* " + e.toJavaString() +
               " *)" + my_semicolon + my_newline); //$NON-NLS-1$ //$NON-NLS-2$
    }

    return spec;
  }

  /**
   * Print the invariant.
   * @param the_invariant invariant to print
   * @return list of lines
   */
  private List < String > printInvariant(final Invariant the_invariant) {
    final List < String > spec = new Vector < String > ();
    if (Beetlz.getProfile().noJml()) return spec;
    if (!the_invariant.isEmpty()) spec.add(my_newline);

    for (final BeetlzExpression e : the_invariant.getNonTrivialPredicates()) {
      spec.add(my_tab + "//@ invariant " + e.toJavaString() +
               my_semicolon + my_newline); //$NON-NLS-1$
    }
    for (final BeetlzExpression e : the_invariant.getInformalPredicates()) {
      spec.add(my_tab + "//@ invariant (* " + e.toJavaString() +
               " *)" + my_semicolon + my_newline); //$NON-NLS-1$ //$NON-NLS-2$
    }

    return spec;
  }

  /**
   * Get the innermost package name.
   * @param the_class class to print
   * @return list of lines
   */
  private String getInnermostPackage(final ClassStructure the_class) {
    final int seven = 7;
    final List < SmartString > p = the_class.getPackage();
    if (p.size() == 0) {
      return ""; //$NON-NLS-1$
    }
    String last = p.get(p.size() - 1).toString();
    if (last.endsWith(BConst.CLUSTER_SUFFIX)) {
      last = last.substring(0, last.length() - seven);
    }

    return PrettyFormatter.formatToJava(last);

  }

  /**
   * Container class for package information.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  private class Package {
    /** Classes in this package. */
    Map < String, List < String > > my_classes;
    /** Name of package. */
    String my_name;

    /**
     * Create a new package.
     * @param a_name name of package
     */
    public Package(final String a_name) {
      my_classes = new HashMap < String, List < String > > ();
      my_name = a_name;
    }
  }
}
