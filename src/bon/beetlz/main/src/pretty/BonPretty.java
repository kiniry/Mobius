/**
 * Package for pretty printers.
 */
package pretty;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.Vector;

import logic.Expression;
import logic.Expression.Nullity;
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
import utils.ModifierManager.ClassType;
import utils.ModifierManager.VisibilityModifier;
import utils.smart.SmartString;

/**
 * Prints pretty printed BON model code.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 * TODO: print AST
 */
public class BonPretty {
  /** Tab. */
  private final String my_tab;
  /** Newline character. */
  private final String my_newline = "\n"; //$NON-NLS-1$
  /** Semicolon character. */
  private final String my_semicolon = ";"; //$NON-NLS-1$

  /**
   * Create a new Bon pretty printer.
   * @param a_tab tab to use
   */
  public BonPretty(final String a_tab) {
    my_tab = a_tab;
  }

  /**
   * Print to files.
   * @param a_dir directory to print to
   * @param the_classes classes to print
   */
  public final void printToFiles(final String a_dir,
                                 final ClassCollection the_classes) {
    final File dir = new File(a_dir);
    if (!dir.exists()) {
      Beetlz.JAVA_LOGGER.
      severe(Beetlz.getResourceBundle().
             getString("BonPretty.directoryDoesNotExist")); //$NON-NLS-1$
      return;
    }
    if (!dir.isDirectory()) {
      Beetlz.JAVA_LOGGER.
      severe(Beetlz.getResourceBundle().
             getString("BonPretty.directoryIsNoDirectory")); //$NON-NLS-1$
    }

    final String fileName = "bon_skeleton.bon"; //to fix //$NON-NLS-1$
    try {
      final BufferedWriter out =
        new BufferedWriter(new FileWriter(dir + "/" +
                                          fileName)); //$NON-NLS-1$
      printClassCollection(the_classes, out);
      out.flush();
      out.close();
    } catch (final IOException e) {
      Beetlz.JAVA_LOGGER.
      severe(String.format(Beetlz.getResourceBundle().
                           getString("BonPretty.cannotWriteFile"),  //$NON-NLS-1$
                           dir, fileName));
    }

  }


  /**
   * Print the classes.
   * @param the_classes classes to print
   * @param the_out where to print
   */
  public final void printClassCollection(final ClassCollection the_classes,
                                   final Writer the_out) {
    final Map < String , List < String[] > > classes =
      this.createTreesFromClasses(the_classes);
    try {
      the_out.write("\nstatic_diagram STATIC_DIAGRAM\n"); //$NON-NLS-1$
      the_out.write("component\n"); //$NON-NLS-1$
      for (final String clusterName : classes.keySet()) {
        if (clusterName.length() == 0) { //default package
          for (final String[] cls : classes.get(clusterName)) {
            for (final String s : cls) {
              the_out.write(my_tab + my_tab + s);
            }
          }
        } else {
          the_out.write(my_tab + "cluster " + clusterName +
                        my_newline + my_newline); //$NON-NLS-1$
          for (final String[] cls : classes.get(clusterName)) {
            for (final String s : cls) {
              the_out.write(my_tab + my_tab + s);
            }
          }

          the_out.write(my_tab + "end" + my_newline + my_newline); //$NON-NLS-1$
        }
      }
      the_out.write("end" + my_newline); //$NON-NLS-1$
      //out.flush();
    } catch (final IOException e) {
      e.printStackTrace();
    }
  }

  /**
   * Pretty print classes.
   * @param the_classes classes to print
   * @return list of lines
   */
  public final Map < String , List < String[] > >
  createTreesFromClasses(final ClassCollection the_classes) {
    final Map < String , List < String[] > > classes =
      new HashMap < String, List < String[] > > ();
    for (final ClassStructure c : the_classes.getClasses()) {
      if (!c.isPrivate()) { //do not print private classes, impl detail
        final String pack = getInnermostPackage(c);
        if (classes.containsKey(pack)) {
          classes.get(pack).add(printClass(c));
        } else {
          final List < String[] > l = new Vector < String[] > ();
          l.add(printClass(c));
          classes.put(pack, l);
        }
      }
    }
    return classes;
  }

  /**
   * Print one class.
   * @param the_class class to print
   * @return list of lines
   */
  private String[] printClass(final ClassStructure the_class) {
    final List < String > list = new Vector < String > ();
    List < String > feat;
    if (Beetlz.getProfile().pureBon()) {
      feat = printAllPureBonFeatures(the_class);
    } else {
      feat = printAllFeatures(the_class);
    }
    final List < String > invariant = printInvariant(the_class);

    list.add(printClassHeader(the_class));
    list.addAll(printClassComments(the_class));
    //list.add("\n");
    list.addAll(printInheritance(the_class));
    list.addAll(feat);
    list.addAll(invariant);
    if (feat.size() > 0 || invariant.size() > 0 || !the_class.getComments().isEmpty()) {
      list.add("end" + my_newline); //$NON-NLS-1$
    }
    list.add(my_newline);
    list.addAll(printClientRelations(the_class));
    list.add(my_newline);

    return list.toArray(new String[list.size()]);
  }

  /**
   * Print class header.
   * @param the_class class to print
   * @return header
   */
  private String printClassHeader(final ClassStructure the_class) {
    String header = ""; //$NON-NLS-1$
    //[deferred | root | effective ]
    if (the_class.isAbstract()) {
      header += "deferred "; //$NON-NLS-1$
    } else if (the_class.isInterface()) {
      header += "deferred "; //$NON-NLS-1$
    } else if (the_class.isRoot()) {
      header += "root "; //$NON-NLS-1$
    } else if (the_class.getInterfaces().size() > 0) {
      header += "effective "; //$NON-NLS-1$
    }

    //class name
    header += "class " + PrettyFormatter.//$NON-NLS-1$
      formatBonClassName(the_class.getName().toString()) + " "; //$NON-NLS-1$

    //[reused, persistent, interfaced]
    if (the_class.isPersistent()) {
      header += "persistent "; //$NON-NLS-1$
    }
    if (the_class.isInterface() || Helper.qualifiesAsBonInterfaced(the_class)) {
      header += "interfaced "; //$NON-NLS-1$
    }

    //Generics
    final List < SmartString > gen = the_class.getGenerics();
    if (gen.size() > 0) {
      header += "["; //$NON-NLS-1$
      for (int i = 0; i < gen.size() - 1; i++) {
        header += PrettyFormatter.getBonType(gen.get(i)) + ", "; //$NON-NLS-1$
      }
      header += PrettyFormatter.getBonType(gen.get(gen.size() - 1));
      header += "]"; //$NON-NLS-1$
    }
    return header + my_newline;
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
      comment.add(BConst.INDEXING + my_newline);
      if (comm.my_about != null && comm.my_about.size() > 0) {
        comment.add(my_tab + BConst.BON_ABOUT + " \"" + //$NON-NLS-1$
                    comm.my_about.get(0).trim() + "\"" + //$NON-NLS-1$
                    my_newline);
        for (int i = 1; i < comm.my_about.size(); i++) {
          comment.add(my_tab + my_tab + "\"" + //$NON-NLS-1$
                      comm.my_about.get(i) + "\"" + //$NON-NLS-1$
                      my_newline);
        }

      }
      if (comm.my_author != null && comm.my_author.length() > 0) {
        comment.add(my_tab + BConst.BON_AUTHOR + " \"" + //$NON-NLS-1$
                    comm.my_author.trim() + "\"" + my_newline); //$NON-NLS-1$
      }
      if (comm.my_version != null && comm.my_version.length() > 0) {
        comment.add(my_tab + BConst.BON_VERSION + " \"" + //$NON-NLS-1$
                    comm.my_version.trim() + "\"" + my_newline); //$NON-NLS-1$
      }
      if (comm.my_allElse != null && comm.my_allElse.length() > 0) {
        comment.add(my_tab + "misc: \"" + comm.my_allElse.trim() + //$NON-NLS-1$
                    "\"" + my_newline); //$NON-NLS-1$
      }
    }
    return comment;
  }

  /**
   * Print inheriatance relations.
   * @param the_class class to print
   * @return list if lines
   */
  private List < String > printInheritance(final ClassStructure the_class) {
    final int two = 2;
    final List < String > inh = new Vector < String > ();
    final List < SmartString > interf =
      new Vector < SmartString > (the_class.getInterfaces());

    String args = ""; //$NON-NLS-1$
    for (final SmartString s : interf) {
      if (!s.toString().equals(BConst.SERIALIZABLE) &&
          !s.toString().equals(BConst.EXTERNALIZABLE) &&
          !s.toString().equals(BConst.RUNNABLE) &&
          !s.toString().equals(BConst.THREAD)) {
        args += PrettyFormatter.getBonType(s) + "; "; //$NON-NLS-1$
      }
    }
    if (args.length() > 0) {
      args = args.substring(0, args.length() - two);
      inh.add("inherit" + my_newline + my_tab); //$NON-NLS-1$
      inh.add(args + my_newline);
    }
    return inh;
  }

  /**
   * Print all features.
   * @param the_class class to print
   * @return list of lines
   */
  private List < String > printAllFeatures(final ClassStructure the_class) {
    final List < String > feature = new Vector < String > ();
    final Map < String, Counter > count = new TreeMap < String, Counter > ();
    if (the_class.hasFeatures() || the_class.isEnum()) {
      //public features & constructors
      List < FeatureStructure > feat = new Vector < FeatureStructure >
      (the_class.getFeatureByVisibility(VisibilityModifier.PUBLIC));
      List < FeatureStructure > constr = new Vector < FeatureStructure >
      (the_class.getConstructorsByVisibility(VisibilityModifier.PUBLIC));
      if (feat.size() > 0 || constr.size() > 0) {
        feature.add("feature" + my_newline); //$NON-NLS-1$
        for (final FeatureStructure f : constr) {
          feature.addAll(printConstructor(f, count,  the_class.getInvariant()));
        }
        for (final FeatureStructure f : feat) {
          if (!Helper.testIsAccessor(the_class, f) &&
              !f.getSimpleName().equals(BConst.METHOD_MAIN)) {
            feature.addAll(printOneFeature(f, count,  the_class.getInvariant()));
          }
        }
      }

      //protected features
      feat = the_class.getFeatureByVisibility(VisibilityModifier.PROTECTED);
      constr = the_class.getConstructorsByVisibility(VisibilityModifier.PROTECTED);
      if (feat.size() > 0 || constr.size() > 0) {
        feature.add("feature{" + PrettyFormatter.//$NON-NLS-1$
                    formatBonClassName(the_class.getSimpleName()) +
                    "}" + my_newline); //$NON-NLS-2$
        for (final FeatureStructure f : constr) {
          feature.addAll(printConstructor(f, count,  the_class.getInvariant()));
        }
        for (final FeatureStructure f : feat) {
          if (!Helper.testIsAccessor(the_class, f) &&
              !f.getSimpleName().equals(BConst.METHOD_MAIN)) {
            feature.addAll(printOneFeature(f, count, the_class.getInvariant()));
          }
        }
      }

      //package-private features
      feat = the_class.getFeatureByVisibility(VisibilityModifier.PACKAGE_PRIVATE);
      constr = the_class.getConstructorsByVisibility(VisibilityModifier.PACKAGE_PRIVATE);
      if (feat.size() > 0 || constr.size() > 0) {
        feature.add("feature{" + getInnermostPackage(the_class) + //$NON-NLS-1$
                    "}" + my_newline); //$NON-NLS-1$
        for (final FeatureStructure f : constr) {
          feature.addAll(printConstructor(f, count, the_class.getInvariant()));
        }
        for (final FeatureStructure f : feat) {
          if (!Helper.testIsAccessor(the_class, f) &&
              !f.getSimpleName().equals(BConst.METHOD_MAIN)) {
            feature.addAll(printOneFeature(f, count, the_class.getInvariant()));
          }
        }
      }

      feat = the_class.getFeatureByVisibility(VisibilityModifier.PRIVATE);
      constr = the_class.getConstructorsByVisibility(VisibilityModifier.PRIVATE);
      if (feat.size() > 0 || constr.size() > 0 || the_class.isEnum()) {
        feature.add("feature{NONE}" + my_newline); //$NON-NLS-1$
        for (final FeatureStructure f : constr) {
          feature.addAll(printConstructor(f, count, the_class.getInvariant()));
        }
        for (final FeatureStructure f : feat) {
          if (!Helper.testIsAccessor(the_class, f) &&
              !f.getSimpleName().equals(BConst.METHOD_MAIN)) {
            feature.addAll(printOneFeature(f, count, the_class.getInvariant()));
          }
        }
        if (the_class.isEnum()) {
          feature.add(my_tab + "enumeration: SET" + my_semicolon + my_newline); //$NON-NLS-1$
        }
      }


    }

    return feature;
  }

  /**
   * Print all features in pure Bon manner.
   * @param the_class class to print
   * @return list of lines
   */
  private List < String > printAllPureBonFeatures(final ClassStructure the_class) {
    final List < String > feature = new Vector < String > ();
    final Map < String, Counter > count = new TreeMap < String, Counter > ();
    if (the_class.hasFeatures()) {
      //public features & constructors
      List < FeatureStructure > feat = new Vector < FeatureStructure >
      (the_class.getFeatureByVisibility(VisibilityModifier.PUBLIC));
      if (feat.size() > 0) {
        feature.add("feature" + my_newline); //$NON-NLS-1$
        for (final FeatureStructure f : feat) {
          feature.addAll(printOneFeature(f, count, the_class.getInvariant()));
        }
      }

      //protected features
      feat = the_class.getFeatureByVisibility(VisibilityModifier.PROTECTED);
      if (feat.size() > 0) {
        feature.add("feature{" + PrettyFormatter.//$NON-NLS-1$
                    formatBonClassName(the_class.getSimpleName()) +
                    "}" + my_newline); //$NON-NLS-1$
        for (final FeatureStructure f : feat) {
          feature.addAll(printOneFeature(f, count, the_class.getInvariant()));
        }
      }

      //package-private features
      feat = the_class.getFeatureByVisibility(VisibilityModifier.PACKAGE_PRIVATE);
      if (feat.size() > 0) {
        feature.add("feature{" + getInnermostPackage(the_class) + //$NON-NLS-1$
                    "}" + my_newline); //$NON-NLS-1$
        for (final FeatureStructure f : feat) {
          feature.addAll(printOneFeature(f, count, the_class.getInvariant()));
        }
      }

      feat = the_class.getFeatureByVisibility(VisibilityModifier.PRIVATE);
      if (feat.size() > 0) {
        feature.add("feature{NONE}" + my_newline); //$NON-NLS-1$
        for (final FeatureStructure f : feat) {
          feature.addAll(printOneFeature(f, count, the_class.getInvariant()));
        }
      }


    }

    return feature;
  }

  /**
   * Print a constructor.
   * @param the_feature feature to print
   * @param the_count count for overloaded features
   * @param the_invariant invariant of the class
   * @return list if lines
   */
  private List < String > printConstructor(final FeatureStructure the_feature,
                                           final Map < String, Counter > the_count,
                                           final Invariant the_invariant) {
    final List < String > c = new Vector < String > ();
    //Name
    String head = ""; //$NON-NLS-1$
    if (!the_count.containsKey(BConst.MAKE)) {
      head += my_tab + BConst.MAKE + my_newline;
      the_count.put(BConst.MAKE, new Counter());
    } else {
      head += my_tab + BConst.MAKE + the_count.get(BConst.MAKE).my_count++ + my_newline;
    }
    c.add(head);
    final Map < String, SmartString > params = the_feature.getSignature().getFormalParameter();
    for (final String s : params.keySet()) {
      c.add(my_tab + my_tab + "-> " + s + ": " +  //$NON-NLS-1$ //$NON-NLS-2$
            PrettyFormatter.getBonType(params.get(s)) + my_newline);
    }
    c.addAll(printFeatureSpec(the_feature, Beetlz.getProfile().nullity(), the_invariant));


    return c;
  }

  /**
   * Print one feature.
   * @param the_feature feature to print
   * @param the_count count for overloaded feature
   * @param the_invariant invariant of the class
   * @return list of lines
   */
  private List < String > printOneFeature(final FeatureStructure the_feature,
                                          final Map < String, Counter > the_count,
                                          final Invariant the_invariant) {
    final List < String > feature = new Vector < String > ();
    //Name
    String head = ""; //$NON-NLS-1$
    if (the_feature.isAbstract()) {
      head += my_tab + "deferred "; //$NON-NLS-1$
    } else if (the_feature.isRedefined()) {
      head += my_tab + "redefined ";  //$NON-NLS-1$
    } else {
      head += my_tab;
    }
    if (!the_count.containsKey(the_feature.getSimpleName())) {
      head += the_feature.getSimpleName();
      the_count.put(the_feature.getSimpleName(), new Counter());
    } else {
      head += the_feature.getSimpleName() +
        the_count.get(the_feature.getSimpleName()).my_count++;
    }

    //Potentially return value
    if (!the_feature.getSignature().getReturnValue().equals(SmartString.getVoid())) {
      head += ": " + PrettyFormatter.//$NON-NLS-1$
        getBonType(the_feature.getSignature().getReturnValue()) +
        my_newline;
    } else {
      head += my_newline;
    }
    feature.add(head);

    //Parameter
    final Map < String, SmartString > params = the_feature.getSignature().getFormalParameter();
    for (final String s : params.keySet()) {
      feature.add(my_tab + my_tab + "-> " + s + ": " +  //$NON-NLS-1$ //$NON-NLS-2$
                  PrettyFormatter.getBonType(params.get(s)) + my_newline);
    }
    feature.addAll(printFeatureSpec(the_feature,
                                    Beetlz.getProfile().nullity(), the_invariant));
    return feature;
  }

  /**
   * Print an invariant.
   * @param the_class class to print
   * @return list of lines
   */
  private List < String > printInvariant(final ClassStructure the_class) {
    final List < String > inv = new Vector < String > ();
    if (Beetlz.getProfile().noJml()) return inv;
    final Invariant i = the_class.getInvariant();
    if (i.getPredicates().size() > 0) {
      inv.add("invariant" + my_newline); //$NON-NLS-1$
      for (final Expression e : i.getNonTrivialPredicates()) {
        inv.add(my_tab + e.toBonString() + my_semicolon + my_newline);
      }
      for (final Expression e : i.getInformalPredicates()) {
        inv.add(my_tab + "-- " + e.toBonString() + my_semicolon + my_newline); //$NON-NLS-1$
      }
    }
    return inv;
  }

  /**
   * Print the feature specification.
   * @param the_feature feature to print
   * @param the_print_nullity do we print nullity
   * @param the_invariant invariant of class
   * @return list of lines
   */
  private List < String > printFeatureSpec(final FeatureStructure the_feature,
                                           final boolean the_print_nullity,
                                           final Invariant the_invariant) {
    if (the_feature.getSpec().isEmpty() ||
        Beetlz.getProfile().noJml()) return new Vector < String > ();

    final Spec s = the_feature.getSpec().get(0);
    final Map < String, SmartString > params = the_feature.getSignature().getFormalParameter();
    final SmartString returnValue = the_feature.getSignature().getReturnValue();
    final List < String > spec = new Vector < String > ();
    final boolean printParamNullity = the_print_nullity &&
      !the_feature.getSignature().defaultParameterNullity(ClassType.BON);
    final boolean printReturnNullity = the_print_nullity &&
      returnValue.getNullity() == Nullity.NON_NULL &&
      !returnValue.equals(SmartString.getVoid());

    final boolean printHistory = the_feature.isCommand() &&
      the_invariant.getHistoryConstraints().size() > 0;

    //precondition
    if (s.getPreconditions().size() > 0 ||
        printParamNullity) {
      spec.add(my_tab + my_tab + "require" + my_newline); //$NON-NLS-1$
      if (printParamNullity) {
        for (final String pName : params.keySet()) {
          if (params.get(pName).getNullity() == Nullity.NON_NULL) {
            spec.add(my_tab + my_tab + my_tab +
                     pName + " /= Void" + my_semicolon + //$NON-NLS-1$
                     my_newline);
          }
        }
      }
      for (final Expression e : s.getNonTrivialPreconditions()) {
        spec.add(my_tab + my_tab + my_tab + e.toBonString() + my_semicolon + my_newline);
      }
      for (final Expression e : s.getInformalPreconditions()) {
        spec.add(my_tab + my_tab + my_tab + "-- " + //$NON-NLS-1$
                 e.toBonString().replace("\n", " ") + //$NON-NLS-1$//$NON-NLS-2$
                 my_semicolon + my_newline);
      }
    }

    //postcondition
    if (s.getPostconditions().size() > 0 || (!s.defaultFrame() && !s.frameIsKeyword()) ||
        s.getConstantValue() != null || printReturnNullity || printHistory) {
      spec.add(my_tab + my_tab + "ensure" + my_newline); //$NON-NLS-1$
      //frame
      if (!s.defaultFrame() && !s.frameIsKeyword()) {
        spec.add(my_tab + my_tab + my_tab + "delta " + //$NON-NLS-1$
                 printFrame(s) + my_semicolon + my_newline);
      }
      //constant value OR non-void
      if (s.getConstantValue() != null) {
        final String cvalue = s.getConstantValue();
        if (cvalue.equals(Spec.UNKNOWN_VALUE)) {
          spec.add(my_tab + my_tab + my_tab +
                   "Result = old " + the_feature.getSimpleName() + //$NON-NLS-1$
                   my_semicolon + my_newline);
        } else if (cvalue.matches("\\d+")) { //$NON-NLS-1$
          spec.add(my_tab + my_tab + my_tab + "Result = " + //$NON-NLS-1$
                   s.getConstantValue() + my_semicolon +
                   my_newline);
        } else {
          spec.add(my_tab + my_tab + my_tab + "Result = \"" + //$NON-NLS-1$
                   s.getConstantValue() + "\"" +  //$NON-NLS-1$
                   my_semicolon + my_newline);
        }
      } else if (printReturnNullity) {
        spec.add(my_tab + my_tab + my_tab + "Result /= Void" + //$NON-NLS-1$
                 my_semicolon + my_newline);
      }
      //Normal post conditions...
      for (final Expression e : s.getNonTrivialPostconditions()) {
        spec.add(my_tab + my_tab + my_tab + e.toBonString() + my_semicolon + my_newline);
      }
      for (final Expression e : s.getInformalPostconditions()) {
        spec.add(my_tab + my_tab + my_tab + "-- " + //$NON-NLS-1$
                 e.toBonString().replace("\n", " ") + //$NON-NLS-1$ //$NON-NLS-2$
                 my_semicolon + my_newline);
      }
      //History constraints
      if (printHistory) {
        for (final Expression e : the_invariant.getNonTrivialHistoryConstraints()) {
          spec.add(my_tab + my_tab + my_tab + e.toBonString() + my_semicolon + my_newline);
        }
        for (final Expression e : the_invariant.getInformalHistoryConstraints()) {
          spec.add(my_tab + my_tab + my_tab + "-- " + //$NON-NLS-1$
                   e.toBonString().replace("\n", " ") + //$NON-NLS-1$ //$NON-NLS-2$
                   my_semicolon + my_newline);
        }
      }
    }

    if (s.getPreconditions().size() > 0 || s.getPostconditions().size() > 0 ||
        (!s.defaultFrame() && !s.frameIsKeyword()) || s.getConstantValue() != null ||
        printParamNullity || printReturnNullity || printHistory) {
      spec.add(my_tab + my_tab + "end\n"); //$NON-NLS-1$
    }

    return spec;
  }

  /**
   * Print client relations.
   * @param the_class class to print
   * @return list of lines
   */
  private List < String > printClientRelations(final ClassStructure the_class) {
    final List < String > rel = new Vector < String > ();
    final String className =
      PrettyFormatter.formatBonClassName(the_class.getName().toString());
    //aggregations, ie member classes:

    for (final SmartString s : the_class.getAggregations()) {
      rel.add(className + " client:{ " + //$NON-NLS-1$
              PrettyFormatter.formatBonClassName(s.toString()) + my_newline);
    }

    //shared associations:
    for (final SmartString s : the_class.getSharedAssociations()) {
      if (Helper.typeKnown(s)) {
        rel.add(className + " client:(1) " + //$NON-NLS-1$
                PrettyFormatter.formatBonClassName(s.toString()) + my_newline);
      }

    }
    return rel;
  }

  /**
   * Get the name of the innermost package.
   * @param the_class class to print
   * @return package name
   */
  private String getInnermostPackage(final ClassStructure the_class) {
    final List < SmartString > p = the_class.getPackage();
    if (p.size() == 0) {
      return ""; //$NON-NLS-1$
    }
    final String last = p.get(p.size() - 1).toString().toUpperCase();
    if (!last.endsWith(BConst.CLUSTER_SUFFIX)) {
      return last + BConst.CLUSTER_SUFFIX;
    } else {
      return last;
    }
  }

  /**
   * Print a feature for external use.
   * @param the_feature feature to print
   * @return string representation
   */
  public static String printPrettyFeature(final FeatureStructure the_feature) {
    String feature = ""; //$NON-NLS-1$
    
    //final int count = 0;
    //Name
    //String head = ""; //$NON-NLS-1$
    //head += the_feature.getSimpleName() + (count == 0 ? "" : count);
    String head = the_feature.getSimpleName();

    //Potentially return value
    if (!the_feature.getSignature().getReturnValue().equals(SmartString.getVoid())) {
      head += ": " +
        PrettyFormatter.getBonType(the_feature.getSignature().getReturnValue()) +
        "\n"; //$NON-NLS-1$ //$NON-NLS-2$
    } else {
      head += "\n"; //$NON-NLS-1$
    }
    feature += head;

    //Parameter
    final Map < String, SmartString > params = the_feature.getSignature().getFormalParameter();
    for (final String s : params.keySet()) {
      feature += "  -> " + s + ": " +  //$NON-NLS-1$ //$NON-NLS-2$
        PrettyFormatter.getBonType(params.get(s)) +
        " (" + params.get(s) + ")\n"; //$NON-NLS-1$ //$NON-NLS-2$
    }


    return feature;
  }

  /**
   * Print a frame condition, method for external use.
   * @param the_spec spec to print
   * @return string representation
   */
  public static String printFrame(final Spec the_spec) {
    String frame = ""; //$NON-NLS-1$

    for (final SmartString str : the_spec.getFrame()) {
      frame += str + ", "; //$NON-NLS-1$
    }
    final int two = 2;
    frame = frame.substring(0, frame.length() - two);
    if (the_spec.getFrame().size() > 1) {
      frame = "{" + frame + "}"; //$NON-NLS-1$ //$NON-NLS-2$
    }
    return frame;
  }

  /**
   * Need an Object to count number of overloaded features.
   * @author Eva Darulova (edarulova@googlemail.com)
   *
   */
  private class Counter {
    /** Counter. */
    int my_count;

    /**
     * Starting count at 0.
     */
    public Counter() {
      my_count = 0;
    }
  }



}
