package log;

import java.util.List;
import java.util.ResourceBundle;
import java.util.SortedSet;
import java.util.TreeSet;

import logic.BeetlzExpression;
import logic.BeetlzExpression.Nullity;
import main.Beetlz;
import structure.ClassStructure;
import structure.FeatureStructure;
import utils.BeetlzSourceLocation;
import utils.FeatureType;
import utils.PrettyFormatter;
import utils.ModifierManager.ClassModifier;
import utils.ModifierManager.FeatureModifier;
import utils.ModifierManager.VisibilityModifier;
import utils.smart.SmartString;
import utils.smart.TypeSmartStringWithLocation;

/**
 * Collects and format consistency checking errors and warnings,
 * as well as major application errors like compilation errors.
 * Creates log records from arguments parsed and formats them to
 * correct target language. Also sorts the records and creates a
 * statistic about how many of each type of errors there are.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class CCLogManager {
  /** Formatting to bon. */
  private final boolean my_to_bon;
  /** Formatter for strings. */
  private final PrettyFormatter my_pretty;
  /** We need to store and sort the entries first. */
  private final SortedSet < CCLogRecord > my_records;
  /** Store errors. */
  private final SortedSet < CCLogRecord > my_errors;

  /**
   * Create a new log manager.
   */
  public CCLogManager() {
    my_records = new TreeSet < CCLogRecord > ();
    my_errors = new TreeSet < CCLogRecord > ();
    my_to_bon = Beetlz.getProfile().javaIsSource();
    my_pretty = new PrettyFormatter(!my_to_bon);
  }

  public void clear() {
    my_records.clear();
    my_errors.clear();
  }

  /* ************************
   * Getter methods
   **************************/
  /**
   * Return all records.
   * @return all records
   */
  public SortedSet < CCLogRecord > getRecords() {
    return my_records;
  }

  /**
   * Get all errors.
   * @return all errors
   */
  public SortedSet < CCLogRecord > getErrors() {
    return my_errors;
  }

  /**
   * Get all records of the specified level.
   * @param the_level level of the records wanted
   * @return all records with level the_level
   */
  public SortedSet < CCLogRecord > getRecords(final CCLevel the_level) {
    final SortedSet < CCLogRecord > list = new TreeSet < CCLogRecord > ();
    for (final CCLogRecord r : my_records) {
      if (r.getLevel() == the_level) {
        list.add(r);
      }
    }
    return list;
  }

  /**
   * Get statistic about the records in this log in string
   * representation. This counts all Java errors and warnings
   * and all JML errors and warnings.
   * @return string with statistics
   */
  public String getStats() {
    int java_err = 0;
    int java_warn = 0;
    int jml_err = 0;
    int jml_warn = 0;
    for (final CCLogRecord r : my_records) {
      if (r.getLevel() == CCLevel.JAVA_ERROR) {
        java_err++;
      } else if (r.getLevel() == CCLevel.JAVA_WARNING) {
        java_warn++;
      } else if (r.getLevel() == CCLevel.JML_ERROR) {
        jml_err++;
      } else if (r.getLevel() == CCLevel.JML_WARNING) {
        jml_warn++;
      }
    }
    
    String java_err_s = java_err == 1 ? "error" : "errors";
    String jml_err_s = jml_err == 1 ? "error" : "errors";
    String java_warn_s = java_warn == 1 ? "error" : "errors";
    String jml_warn_s = jml_warn == 1 ? "error" : "errors";

    return String.format("%d Structure %s, %d Structure %s, %d Specification %s and %s Specification %s found.", //$NON-NLS-1$
        java_err, java_err_s, java_warn, java_warn_s,
        jml_err, jml_err_s, jml_warn, jml_warn_s);
  }

  public void setToJava(boolean toJava) {
    my_pretty.setToJava(toJava);
  }

  /**
   * All any records in batch. Any records with level
   * CCLevel.COMPILATION_ERROR will be added to errors.
   * @param the_records records to be added
   */
  public void addRecords(final List < CCLogRecord > the_records) {
    for (final CCLogRecord r : the_records) {
      if (r.getLevel() == CCLevel.COMPILATION_ERROR) {
        my_errors.add(r);
      } else {
        my_records.add(r);
      }
    }
  }

  /**
   * Incorrect mapping in user settings file.
   * @param the_src source location of error
   * @param a_mapping mapping that is faulty
   */
  public void logIncorrectMapping(final BeetlzSourceLocation the_src, final String a_mapping) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("The mapping for %s is not correct.", //$NON-NLS-1$
            a_mapping)));
  }

  /**
   * Incorrect feature type (query or command).
   * @param the_src source location of error
   * @param a_class enclosing class of faulty feature/method
   * @param a_feature faulty feature/method name
   * @param the_expected expected feature type
   * @param the_found actually found feature type
   */
  public void logIncorrectFeatureType(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final FeatureType the_expected,
      final FeatureType the_found) {
    my_records.add(new CCLogRecord(CCLevel.JML_WARNING, the_src,
        String.format("%s@%s expected %s but found %s.", //$NON-NLS-1$
            a_feature, a_class,
            the_expected, the_found)));
  }

  /**
   * Incorrect frame condition.
   * @param the_src source location of error
   * @param a_class enclosing class of faulty feature/method
   * @param a_feature faulty feature/method name
   * @param the_expected expected frame condition
   * @param the_found actually found frame condition
   */
  public void logIncorrectFrameCondition(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final String the_expected,
      final String the_found) {
//    my_records.add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
//        String.format(Beetlz.getResourceBundle().
//            getString("CCLogManager." +
//            "incorrectFrameCondMsg"),  //$NON-NLS-1$
//            a_feature, a_class,
//            the_expected, the_found)));
    //TODO re-enable
  }

  /**
   * Incorrect class generics.
   * @param the_src source location of error
   * @param a_class class with incorrect generics
   * @param the_expected expected generic
   * @param the_found actually found generic
   */
  public void logIncorrectGenerics(final BeetlzSourceLocation the_src, final SmartString a_class,
      final SmartString the_expected,
      final SmartString the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s expected generic parameter %s but found %s",  //$NON-NLS-1$
            a_class, my_pretty.getType(the_expected),
            my_pretty.getType(the_found))));
  }

  /**
   * Incorrect number of generic parameters.
   * @param the_src source location of error
   * @param a_class class with incorrect generics
   * @param the_expected expected number of generic parameters
   * @param the_found actually found number of generic parameters
   */
  public void logIncorrectGenericsNumber(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final int the_expected, final int the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s expected number of generic parameters %d but found %d.", //$NON-NLS-1$
            a_class, the_expected, the_found)));
  }

  /**
   * Incorrect modifier.
   * @param the_src source location of error
   * @param a_class class with faulty feature/method
   * @param a_feature feature/method with incorrect modifier
   * @param the_expected expected modifier
   * @param the_found actually found modifier
   */
  public void logIncorrectModifier(final BeetlzSourceLocation the_src, final SmartString a_class,
      final SmartString a_feature,
      final FeatureModifier the_expected,
      final FeatureModifier the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s@%s expected %s but found %s.", //$NON-NLS-1$
            a_feature, a_class,
            my_pretty.getFeatMod(the_expected),
            my_pretty.getFeatMod(the_found))));
  }

  /**
   * Incorrect visibility modifier (ie public, protected, private).
   * @param the_src source location of error
   * @param a_class class with faulty feature/method
   * @param a_feature feature/method with incorrect visibility modifier
   * @param the_expected expected modifier
   * @param the_found actually found modifier
   */
  public void logIncorrectVisibilityModifier(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final VisibilityModifier the_expected,
      final VisibilityModifier the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s@%s expected %s but found %s.", //$NON-NLS-1$
            a_feature, a_class,
            the_expected, the_found)));
  }

  /**
   * Incorrect return type.
   * @param the_src source location of error
   * @param a_class class with faulty feature/method
   * @param a_feature feature/method with incorrect return type
   * @param the_expected expected return type
   * @param the_found actually found return type
   */
  public void logIncorrectReturnType(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final SmartString the_expected,
      final SmartString the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s@%s expected return type %s but found %s.", //$NON-NLS-1$
            a_feature, a_class,
            my_pretty.getType(the_expected),
            my_pretty.getType(the_found))));
  }

  /**
   * Incorrect frame condition default value.
   * @param the_src source location of error
   * @param a_class class with faulty feature/method
   * @param a_feature feature/method with incorrect frame default
   * @param the_expected expected default
   * @param the_found actually found default
   */
  public void logIncorrectFrameDefault(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final String the_expected,
      final String the_found) {
//    my_records.add(new CCLogRecord(CCLevel.JML_WARNING, the_src,
//        String.format(Beetlz.getResourceBundle().
//            getString("CCLogManager." +
//            "incorrectFrameDefaultMsg"), //$NON-NLS-1$
//            a_feature, a_class,
//            the_expected, the_found)));
  //TODO re-enable
  }

  /**
   * Incorrect return type nullity.
   * By nullity we mean whether a variable is allowed to
   * be null or void.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature/method with error
   * @param the_expected expected nullity
   * @param the_found actually found nullity
   */
  public void logIncorrectReturnTypeNullity(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final Nullity the_expected,
      final Nullity the_found) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_WARNING, the_src,
        String.format("%s@%s return value expected %s, found %s.", //$NON-NLS-1$
            a_feature, a_class,
            PrettyFormatter.getNullity(the_expected),
            PrettyFormatter.getNullity(the_found))));
  }

  /**
   * Incorrect parameter type nullity.
   * By nullity we mean whether a formal parameter is allowed to
   * be null or void.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with incorrect nullity
   */
  public void logIncorrectParameterTypeNullity(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_WARNING, the_src,
        String.format("%s@%s has incorrect formal parameter nullity.", //$NON-NLS-1$
            a_feature, a_class)));
  }

  /**
   * Incorrect enclosing package or cluster.
   * @param the_src source location of error
   * @param a_class class with incorrect package
   * @param the_expected expected package
   * @param the_found actually found package
   */
  public void logIncorrectPackage(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString the_expected,
      final SmartString the_found) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
          String.format("%s has incorrect package; expected %s, found %s.",  //$NON-NLS-1$
              a_class, the_expected.toString(),
              the_found.toString())));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
          String.format("%s has incorrect cluster; expected %s, found %s.",  //$NON-NLS-1$
              a_class, the_expected.toString(),
              the_found.toString())));
    }
  }


  /* *************************************************
   * Logging Missing ...
   ***************************************************/

  /**
   * Missing features.
   * @param the_src source location of error
   * @param a_class class where feature is missing
   * @param the_features list of features that are missing.
   */
  public void logMissingFeature(final SmartString a_class, final List < FeatureStructure > the_features, final List<ClassStructure> the_classes) {
    for (int i=0; i < the_features.size(); i++) {
      FeatureStructure fS = the_features.get(i);
      ClassStructure cS = the_classes.get(i);
      
      if (cS.getSourceLocation().isJavaFile()) {
        my_records.
        add(new CCLogRecord(CCLevel.JAVA_ERROR, cS.getSourceLocation(),
            String.format("%s is missing method %s.", //$NON-NLS-1$
                a_class, fS.getSimpleName())));
      } else {
        my_records.
        add(new CCLogRecord(CCLevel.JAVA_ERROR, cS.getSourceLocation(),
            String.format("%s is missing feature(s) %s.", //$NON-NLS-1$
                a_class, fS.getSimpleName())));
      }
    }

  }

  /**
   * Missing constructor.
   * @param the_src source location of error
   * @param a_class class with missing constructor
   */
  public void logMissingConstructor(final BeetlzSourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s is missing a constructor.",  //$NON-NLS-1$
            a_class)));
  }

  /**
   * Missing interface or parent class.
   * @param the_src source location of error
   * @param a_class class with missing interface
   * @param a_missing_cls name of missing interface
   */
  public void logMissingInterface(final BeetlzSourceLocation the_src, final SmartString a_class,
      final SmartString a_missing_cls) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
          String.format("%s is missing interface or super class %s.", //$NON-NLS-1$
              a_class, my_pretty.getClassName(a_missing_cls))));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
          String.format("%s is missing super class %s.", //$NON-NLS-1$
              a_class, my_pretty.getClassName(a_missing_cls))));
    }
  }

  /**
   * Missing shared association.
   * A shared association is a (final) reference to a class
   * in the model. So in general references to class from
   * the standard library are not considered shared
   * references.
   * @param the_src source location of error
   * @param the_class class with missing association
   * @param a_missing_cls missing association
   */
  public void logMissingSharedAssociation(final BeetlzSourceLocation the_src,
      final SmartString the_class,
      final SmartString a_missing_cls) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("%s is missing a shared association with %s.", //$NON-NLS-1$
            the_class,
            my_pretty.getClassName(a_missing_cls))));
  }

  /**
   * Missing aggregation or member class.
   * @param the_src source location of error
   * @param the_class class with missing aggregation
   * @param a_missing_cls name of missing aggregation/member class
   */
  public void logMissingAggregation(final BeetlzSourceLocation the_src, final SmartString the_class,
      final SmartString a_missing_cls) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
          String.format("%s is missing member class %s.",  //$NON-NLS-1$
              the_class, my_pretty.getClassName(a_missing_cls))));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
          String.format("%s is missing aggregation class %s.",  //$NON-NLS-1$
              the_class, my_pretty.getClassName(a_missing_cls))));
    }
  }

  /**
   * Missing invariant.
   * @param the_src source location of error
   * @param a_class name of class that is missing invariant
   */
  public void logMissingInvariant(final BeetlzSourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s is missing an invariant.", //$NON-NLS-1$
            a_class)));
  }

  /**
   * Missing invariant clauses.
   * @param the_src source location of error
   * @param a_class name of class with missing invariants
   * @param the_clauses clauses that are missing
   */
  public void logMissingInvariantClauses(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final List < BeetlzExpression > the_clauses) {
    String clauses = ""; //$NON-NLS-1$
    for (final BeetlzExpression s : the_clauses) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s is missing these invariant clauses: %s", //$NON-NLS-1$
            a_class, clauses)));
  }

  /**
   * Missing formal parameters in signature.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with missing formal parameters
   * @param some_params list of missing parameters
   */
  public void logMissingParameter(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final List < SmartString > some_params) {
    String list = ""; //$NON-NLS-1$
    final int two = 2;
    for (final SmartString s : some_params) {
      list += my_pretty.getType(s) + ", "; //$NON-NLS-1$
    }
    list = list.substring(0, list.length() - two);
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s@%s is missing parameter type(s) %s.", //$NON-NLS-1$
            a_feature, a_class, list)));
  }

  /**
   * Missing postcondition.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with missing postcondition
   * @param the_post list of missing postconditions
   */
  public void logMissingPostcondition(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final List < BeetlzExpression > the_post) {
    String clauses = ""; //$NON-NLS-1$
    for (final BeetlzExpression s : the_post) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s@%s is missing postcondition: %s", //$NON-NLS-1$
            a_feature, a_class, clauses)));
  }

  /**
   * Missing preconditions.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with missing precondition
   * @param the_pre list of missing preconditions
   */
  public void logMissingPrecondition(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final List < BeetlzExpression > the_pre) {
    String clauses = ""; //$NON-NLS-1$
    for (final BeetlzExpression s : the_pre) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s@%s is missing precondition: %s",  //$NON-NLS-1$
            a_feature, a_class, clauses)));
  }

  /**
   * Missing frame condition.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with missing frame condition
   * @param a_frame name of missing condition
   */
  public void logMissingFrameCondition(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final SmartString a_frame) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s@%s is missing a frame condition: %s.", //$NON-NLS-1$
            a_feature, a_class, a_frame)));
  }

  /**
   * Missing history constraint or postcondition on
   * a constructor.
   * @param the_src source location of error
   * @param the_class class with missing history constraint
   * @param the_cond constraint missing
   */
  public void logMissingHistoryContraint(final BeetlzSourceLocation the_src,
      final SmartString the_class,
      final BeetlzExpression the_cond) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s is missing a history constraint:\n\t %s.", //$NON-NLS-1$
            the_class, the_cond.toBonString())));
  }


  /* **************************************************
   * Logging Different
   ****************************************************/

  /**
   * Class not found.
   * @param a_cls name of class not found.
   */
  public void logClassNotFound(final TypeSmartStringWithLocation a_cls) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, a_cls.getLocation(),
        String.format("No mapping for class %s found.",  //$NON-NLS-1$
            my_pretty.getClassName(a_cls))));
  }


  /**
   * All features/methods/fields are expected to be public.
   * @param the_src source location of error
   * @param a_class class with not all features public
   */
  public void logExpectedAllPublic(final BeetlzSourceLocation the_src, final SmartString a_class) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
          String.format("%s: expected all methods public.", //$NON-NLS-1$
              a_class)));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
          String.format("%s: expected all features public.", //$NON-NLS-1$
              a_class)));
    }
  }

  /**
   * Expected a class modifier not found.
   * @param the_src source location of error
   * @param a_class class with missing modifier
   * @param the_expected expected modifier
   */
  public void logExpectedClassModifier(final BeetlzSourceLocation the_src, final SmartString a_class,
      final ClassModifier the_expected) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s is expected to be %s.", //$NON-NLS-1$
            a_class, my_pretty.getClassMod(the_expected))));
  }

  /**
   * Expected a feature modifier not found.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature missing a modifier
   * @param the_expected expected modifier
   */
  public void logExpectedFeatureModifier(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final FeatureModifier the_expected) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s@%s is expected %s", //$NON-NLS-1$
            a_class, a_feature,
            my_pretty.getFeatMod(the_expected))));
  }

  /**
   * Expected a feature modifier not found, only warning.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature missing a modifier
   * @param the_expected expected modifier
   */
  public void logExpectedFeatureModifierWarning(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final FeatureModifier the_expected) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("%s@%s is expected %s", //$NON-NLS-1$
            a_class, a_feature,
            my_pretty.getFeatMod(the_expected))));
  }

  /**
   * Class is expected to be an enumerated type.
   * @param the_src source location of error
   * @param a_class name of class expected to be enum
   */
  public void logExpectedEnum(final BeetlzSourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("%s is expected to be an enumerated type.", //$NON-NLS-1$
            a_class)));
  }

  /**
   * Multiple potential matches found for one class.
   * @param a_class class name with multiple matches
   */
  public void logMultipleClasses(final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, null,
        String.format("Error: Multiple potential matches have been found for %s.", //$NON-NLS-1$
            a_class)));
  }

  /**
   * A class is not accessible, ie private.
   * @param the_src source location of error
   * @param a_class not accessible class
   */
  public void logNotAccessible(final BeetlzSourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s is private and not accessible.", //$NON-NLS-1$
            a_class)));
  }

  /**
   * Class has a redundant enclosing class (aggregation).
   * @param the_src source location of error
   * @param a_class class with redundant enclosing class
   * @param the_found redundant enclosing class
   */
  public void logRedundantEnclosingClass(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString the_found) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("%s has a redundant enclosing class %s.", //$NON-NLS-1$
            a_class, the_found)));
  }

  /**
   * Redundant interface.
   * @param the_src source location of error
   * @param a_class class with redundant interface
   * @param a_redundant_cls redundant interface name
   */
  public void logRedundantInterface(final BeetlzSourceLocation the_src, final SmartString a_class,
      final SmartString a_redundant_cls) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s is a redundant interface for %s.", //$NON-NLS-1$
            a_redundant_cls, a_class)));
  }

  /**
   * Redundant constructor.
   * @param the_src source location of error
   * @param the_class class with redundant constructor
   */
  public void logRedundantConstructor(final BeetlzSourceLocation the_src,
      final SmartString the_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s has a redundant constructor.", //$NON-NLS-1$
            the_class)));
  }

  /**
   * Redundant shared association.
   * @param the_src source location of error
   * @param the_class class with redundant shared association
   * @param the_redundant_ass name of redundant associated class
   */
  public void logRedundantSharedAssociation(final BeetlzSourceLocation the_src,
      final SmartString the_class,
      final SmartString the_redundant_ass) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("%s has a redundant shared association %s.",  //$NON-NLS-1$
            the_class, the_redundant_ass)));
  }

  /**
   * Redundant aggregation.
   * @param the_src source location of error
   * @param the_class class with redundant aggregation
   * @param the_redundant_ass name of redundant aggregated class
   */
  public void logRedundantAggregation(final BeetlzSourceLocation the_src,
      final SmartString the_class,
      final SmartString the_redundant_ass) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
          String.format("%s has a redundant enclosing class %s.", //$NON-NLS-1$
              the_class, the_redundant_ass)));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
          String.format("%s has a redundant aggregation class %s.", //$NON-NLS-1$
              the_class, the_redundant_ass)));
    }
  }

  /**
   * Redundant features.
   * @param the_src source location of error
   * @param a_class class with redundant features
   * @param the_features list of redundant features
   */
  public void logRedundantFeature(final SmartString a_class, final List < FeatureStructure > the_features) {
    for (FeatureStructure fS : the_features) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, fS.getSourceLoc(),
          String.format("Feature %s in %s has no mapping.", //$NON-NLS-1$
              fS.getSimpleName(), a_class)));
    }
  }

  /**
   * A class should not have a modifier is has.
   * @param the_src source location of error
   * @param a_class class with additional modifier
   * @param a_should_not modifier that should not be present
   */
  public void logShouldNotClassModifier(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final ClassModifier a_should_not) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("%s should not be %s.", //$NON-NLS-1$
            a_class, my_pretty.getClassMod(a_should_not))));
  }

  /**
   * A class should not have a modifier is has.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with additional modifier
   * @param a_should_not modifier it should not have
   */
  public void logShouldNotFeatureModifierWarning(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final FeatureModifier a_should_not) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("%s@%s should not be %s.", //$NON-NLS-1$
            a_feature, a_class,
            my_pretty.getFeatMod(a_should_not))));
  }

  /**
   * A class should not be an enumerated type.
   * @param the_src source location of error
   * @param a_class name of class that should not be enumerated
   */
  public void logShouldNotEnum(final BeetlzSourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
        String.format("%s should not be an enumerated type.", //$NON-NLS-1$
            a_class)));
  }

  /**
   * A feature has too many parameters.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with too many parameters
   * @param some_params list of additional parameters
   */
  public void logTooManyParameter(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final List < SmartString > some_params) {
    String list = ""; //$NON-NLS-1$
    final int two = 2;
    for (final SmartString s : some_params) {
      list += my_pretty.getType(s) + ", "; //$NON-NLS-1$
    }
    list = list.substring(0, list.length() - two);
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
        String.format("%s@%s has unexpected arguments %s", //$NON-NLS-1$
            a_feature, a_class, list)));
  }

  /**
   * A feature has too many preconditions.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with too many preconditions
   * @param the_pre list of additional preconditions
   */
  public void logTooManyPrecondition(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final List < BeetlzExpression > the_pre) {
    String clauses = ""; //$NON-NLS-1$
    for (final BeetlzExpression s : the_pre) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s@%s has a surplus precondition(s): %s", //$NON-NLS-1$
            a_feature, a_class, clauses)));
  }

  /**
   * A feature has too many postconditions.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with too many postconditions
   * @param the_post list of additional postconditions
   */
  public void logTooManyPostcondition(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature,
      final List < BeetlzExpression > the_post) {
    String clauses = ""; //$NON-NLS-1$
    for (final BeetlzExpression s : the_post) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s@%s has a surplus postcondition(s): %s", //$NON-NLS-1$
            a_feature, a_class, clauses)));
  }

  /**
   * A class has too many invariants.
   * @param the_src source location of error
   * @param a_class class with too many invariants
   * @param the_inv list of additional invariants
   */
  public void logTooManyInvariant(final BeetlzSourceLocation the_src, final SmartString a_class,
      final List < BeetlzExpression > the_inv) {
    String clauses = ""; //$NON-NLS-1$
    for (final BeetlzExpression s : the_inv) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
        String.format("%s has a surplus invariants: %s", //$NON-NLS-1$
            a_class, clauses)));
  }

  /* ***********************
   * General notes
   *************************/
  /**
   * General note about the not entirely matching correspondence
   * of the 'redefined' modifier with the '@Override' annotations.
   * @param the_src source location of error
   * @param a_class class with redefined modifier or Override annotation
   * @param a_feature feature with modifier or annotation
   */
  public void logRedefinedCorrespondence(final BeetlzSourceLocation the_src,
      final SmartString a_class,
      final SmartString a_feature) {
    my_records.
    add(new CCLogRecord(CCLevel.GENERAL_NOTE, the_src,
        String.format("Compatibility warning for %s@%s: " + //$NON-NLS-1$
        		"@Override and 'redefined' do not correspond exactly. " + //$NON-NLS-1$
        		"A redefined feature cannot be deferred, " + //$NON-NLS-1$
        		"whereas an abstract method may have annotation @Override.", //$NON-NLS-1$
            a_class, a_feature)));
  }

  /**
   * General note about the different defaults for
   * frame conditions.
   */
  public void logAssignableDefaultCorrespondence() {
    my_records.
    add(new CCLogRecord(CCLevel.GENERAL_NOTE, null,
        String.format("BON and Java have different default frame conditions:\n" + //$NON-NLS-1$
        		"\t\tin BON all queries are automatically pure,\n " + //$NON-NLS-1$
        		"\t\twhereas in Java the default is 'assignable \\everything'."))); //$NON-NLS-1$

  }

  /**
   * General note about the different nullity defaults.
   */
  public void logNullityDefaultCorrespondence() {
    my_records.
    add(new CCLogRecord(CCLevel.GENERAL_NOTE, null,
        String.format("BON and Java have different default nullity:\n" + //$NON-NLS-1$
        		"\t\tin BON all types are automatically nullable,\n" + //$NON-NLS-1$
        		"\t\twhereas in Java the default is non-null."))); //$NON-NLS-1$
  }

  /**
   * General note that generic methods are not supported.
   * @param the_src source location of error
   * @param the_class class with generic method
   * @param the_method method with generic parameters
   */
  public void logGenericMethodNotSupported(final BeetlzSourceLocation the_src,
      final SmartString the_class,
      final SmartString the_method) {
    my_records.
    add(new CCLogRecord(CCLevel.GENERAL_NOTE, the_src,
        String.format("%s@%s is generic. BON does not support generic methods.",  //$NON-NLS-1$
            the_method, the_class)));
  }

  /**
   * General note about the entirely matching correspondence
   * of history constraints.
   */
  public void logHistoryConstraints() {
    my_records.add(new CCLogRecord(CCLevel.GENERAL_NOTE, null,
        "Technically history constraints found in Java should be appended to " + //$NON-NLS-1$
        "EVERY postcondition in BON.\nPlease note, that it is only being " + //$NON-NLS-1$
        "checked that each constraint appears ONCE somewhere in the class.")); //$NON-NLS-1$
  }
}
