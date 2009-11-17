package log;

import java.util.List;
import java.util.ResourceBundle;
import java.util.SortedSet;
import java.util.TreeSet;

import logic.Expression;
import logic.Expression.Nullity;
import main.Beetlz;
import structure.FeatureStructure;
import utils.FeatureType;
import utils.PrettyFormatter;
import utils.SourceLocation;
import utils.ModifierManager.ClassModifier;
import utils.ModifierManager.FeatureModifier;
import utils.ModifierManager.VisibilityModifier;
import utils.smart.SmartString;

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
    ResourceBundle rb = Beetlz.getResourceBundle();
    String java_err_s = rb.getString(java_err == 1 ? "CCLogManager.errorSingular" : "CCLogManager.errorPlural");
    String jml_err_s = rb.getString(jml_err == 1 ? "CCLogManager.errorSingular" : "CCLogManager.errorPlural");
    String java_warn_s = rb.getString(java_warn == 1 ? "CCLogManager.warningSingular" : "CCLogManager.warningPlural");
    String jml_warn_s = rb.getString(jml_warn == 1 ? "CCLogManager.warningSingular" : "CCLogManager.warningPlural");
    
    return String.format(rb.getString("CCLogManager.errorStats"), //$NON-NLS-1$
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
  public void logIncorrectMapping(final SourceLocation the_src, final String a_mapping) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectMappingMsg"), //$NON-NLS-1$
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
  public void logIncorrectFeatureType(final SourceLocation the_src,
                                      final SmartString a_class,
                                      final SmartString a_feature,
                                      final FeatureType the_expected,
                                      final FeatureType the_found) {
    my_records.add(new CCLogRecord(CCLevel.JML_WARNING, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectFeatureTypeMsg"), //$NON-NLS-1$
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
  public void logIncorrectFrameCondition(final SourceLocation the_src,
                                         final SmartString a_class,
                                         final SmartString a_feature,
                                         final String the_expected,
                                         final String the_found) {
    my_records.add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectFrameCondMsg"),  //$NON-NLS-1$
                                                 a_feature, a_class,
                                                 the_expected, the_found)));
  }

  /**
   * Incorrect class generics.
   * @param the_src source location of error
   * @param a_class class with incorrect generics
   * @param the_expected expected generic
   * @param the_found actually found generic
   */
  public void logIncorrectGenerics(final SourceLocation the_src, final SmartString a_class,
                                   final SmartString the_expected,
                                   final SmartString the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectGenericsMsg"),  //$NON-NLS-1$
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
  public void logIncorrectGenericsNumber(final SourceLocation the_src,
                                         final SmartString a_class,
                                         final int the_expected, final int the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectGenericsNumberMsg"), //$NON-NLS-1$
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
  public void logIncorrectModifier(final SourceLocation the_src, final SmartString a_class,
                                   final SmartString a_feature,
                                   final FeatureModifier the_expected,
                                   final FeatureModifier the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectModifierMsg"), //$NON-NLS-1$
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
  public void logIncorrectVisibilityModifier(final SourceLocation the_src,
                                             final SmartString a_class,
                                             final SmartString a_feature,
                                             final VisibilityModifier the_expected,
                                             final VisibilityModifier the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectVisibilityMsg"), //$NON-NLS-1$
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
  public void logIncorrectReturnType(final SourceLocation the_src,
                                     final SmartString a_class,
                                     final SmartString a_feature,
                                     final SmartString the_expected,
                                     final SmartString the_found) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectRetrunTypeMsg"), //$NON-NLS-1$
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
  public void logIncorrectFrameDefault(final SourceLocation the_src,
                                       final SmartString a_class,
                                       final SmartString a_feature,
                                       final String the_expected,
                                       final String the_found) {
    my_records.add(new CCLogRecord(CCLevel.JML_WARNING, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "incorrectFrameDefaultMsg"), //$NON-NLS-1$
                                                 a_feature, a_class,
                                                 the_expected, the_found)));
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
  public void logIncorrectReturnTypeNullity(final SourceLocation the_src,
                                            final SmartString a_class,
                                            final SmartString a_feature,
                                            final Nullity the_expected,
                                            final Nullity the_found) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "incorrectReturnTypeNullityMsg"), //$NON-NLS-1$
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
  public void logIncorrectParameterTypeNullity(final SourceLocation the_src,
                                               final SmartString a_class,
                                               final SmartString a_feature) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "incorrectParameterNullityMsg"), //$NON-NLS-1$
                                      a_feature, a_class)));
  }

  /**
   * Incorrect enclosing package or cluster.
   * @param the_src source location of error
   * @param a_class class with incorrect package
   * @param the_expected expected package
   * @param the_found actually found package
   */
  public void logIncorrectPackage(final SourceLocation the_src,
                                  final SmartString a_class,
                                  final SmartString the_expected,
                                  final SmartString the_found) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "incorrectPackageMsgJava"),  //$NON-NLS-1$
                                        a_class, the_expected.toString(),
                                        the_found.toString())));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "incorrectPackageMsgBon"),  //$NON-NLS-1$
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
  public void logMissingFeature(final SourceLocation the_src, final SmartString a_class,
                                final List < String > the_features) {
    String list = ""; //$NON-NLS-1$
    final int two = 2;
    for (final String s : the_features) {
      list += s + ", "; //$NON-NLS-1$
    }
    if (list.length() > two) list = list.substring(0, list.length() - two);
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "missingMethodsMsg"), //$NON-NLS-1$
                                        a_class, list)));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "missingFeaturesMsg"), //$NON-NLS-1$
                                        a_class, list)));
    }
  }

  /**
   * Missing constructor.
   * @param the_src source location of error
   * @param a_class class with missing constructor
   */
  public void logMissingConstructor(final SourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "missingConstructorMsg"),  //$NON-NLS-1$
                                      a_class)));
  }

  /**
   * Missing interface or parent class.
   * @param the_src source location of error
   * @param a_class class with missing interface
   * @param a_missing_cls name of missing interface
   */
  public void logMissingInterface(final SourceLocation the_src, final SmartString a_class,
                                  final SmartString a_missing_cls) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "missingInterfaceSuperclassMsg"), //$NON-NLS-1$
                                        a_class, my_pretty.getClassName(a_missing_cls))));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "missingSuperclassMsg"), //$NON-NLS-1$
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
  public void logMissingSharedAssociation(final SourceLocation the_src,
                                          final SmartString the_class,
                                          final SmartString a_missing_cls) {
    my_records.add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                                   String.format(Beetlz.getResourceBundle().
                                                 getString("CCLogManager." +
                                                 "missingSharedAssociationMsg"), //$NON-NLS-1$
                                                 the_class,
                                                 my_pretty.getClassName(a_missing_cls))));
  }

  /**
   * Missing aggregation or member class.
   * @param the_src source location of error
   * @param the_class class with missing aggregation
   * @param a_missing_cls name of missing aggregation/member class
   */
  public void logMissingAggregation(final SourceLocation the_src, final SmartString the_class,
                                    final SmartString a_missing_cls) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "missingAggregationMsgJava"),  //$NON-NLS-1$
                                        the_class, my_pretty.getClassName(a_missing_cls))));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "missingAggregationMsgBon"),  //$NON-NLS-1$
                                        the_class, my_pretty.getClassName(a_missing_cls))));
    }
  }

  /**
   * Missing invariant.
   * @param the_src source location of error
   * @param a_class name of class that is missing invariant
   */
  public void logMissingInvariant(final SourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "missingInvariantMsg"), //$NON-NLS-1$
                                      a_class)));
  }

  /**
   * Missing invariant clauses.
   * @param the_src source location of error
   * @param a_class name of class with missing invariants
   * @param the_clauses clauses that are missing
   */
  public void logMissingInvariantClauses(final SourceLocation the_src,
                                         final SmartString a_class,
                                         final List < Expression > the_clauses) {
    String clauses = ""; //$NON-NLS-1$
    for (final Expression s : the_clauses) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "missingInvariantClausesMsg"), //$NON-NLS-1$
                                      a_class, clauses)));
  }

  /**
   * Missing formal parameters in signature.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with missing formal parameters
   * @param some_params list of missing parameters
   */
  public void logMissingParameter(final SourceLocation the_src,
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
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "missingParameterTypesMsg"), //$NON-NLS-1$
                                      a_feature, a_class, list)));
  }

  /**
   * Missing postcondition.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with missing postcondition
   * @param the_post list of missing postconditions
   */
  public void logMissingPostcondition(final SourceLocation the_src,
                                      final SmartString a_class,
                                      final SmartString a_feature,
                                      final List < Expression > the_post) {
    String clauses = ""; //$NON-NLS-1$
    for (final Expression s : the_post) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "missingPostconditionMsg"), //$NON-NLS-1$
                                      a_feature, a_class, clauses)));
  }

  /**
   * Missing preconditions.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with missing precondition
   * @param the_pre list of missing preconditions
   */
  public void logMissingPrecondition(final SourceLocation the_src,
                                     final SmartString a_class,
                                     final SmartString a_feature,
                                     final List < Expression > the_pre) {
    String clauses = ""; //$NON-NLS-1$
    for (final Expression s : the_pre) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "missingPreconditionMsg"),  //$NON-NLS-1$
                                      a_feature, a_class, clauses)));
  }

  /**
   * Missing frame condition.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with missing frame condition
   * @param a_frame name of missing condition
   */
  public void logMissingFrameCondition(final SourceLocation the_src,
                                       final SmartString a_class,
                                       final SmartString a_feature,
                                       final SmartString a_frame) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "missingFrameConditionMsg"), //$NON-NLS-1$
                                      a_feature, a_class, a_frame)));
  }

  /**
   * Missing history constraint or postcondition on
   * a constructor.
   * @param the_src source location of error
   * @param the_class class with missing history constraint
   * @param the_cond constraint missing
   */
  public void logMissingHistoryContraint(final SourceLocation the_src,
                                         final SmartString the_class,
                                         final Expression the_cond) {
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "missingHistoryConstraintMsg"), //$NON-NLS-1$
                                      the_class, the_cond.toBonString())));
  }


  /* **************************************************
   * Logging Different
   ****************************************************/

  /**
   * Class not found.
   * @param a_cls name of class not found.
   */
  public void logClassNotFound(final SmartString a_cls) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, null,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "classNotFoundMsg"),  //$NON-NLS-1$
                                      my_pretty.getClassName(a_cls))));
  }


  /**
   * All features/methods/fields are expected to be public.
   * @param the_src source location of error
   * @param a_class class with not all features public
   */
  public void logExpectedAllPublic(final SourceLocation the_src, final SmartString a_class) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "expectedPublicMsgJava"), //$NON-NLS-1$
                                        a_class)));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "expectedPublicMsgBon"), //$NON-NLS-1$
                                        a_class)));
    }
  }

  /**
   * Expected a class modifier not found.
   * @param the_src source location of error
   * @param a_class class with missing modifier
   * @param the_expected expected modifier
   */
  public void logExpectedClassModifier(final SourceLocation the_src, final SmartString a_class,
                                       final ClassModifier the_expected) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "expectedClassModifierMsg"), //$NON-NLS-1$
                                      a_class, my_pretty.getClassMod(the_expected))));
  }

  /**
   * Expected a feature modifier not found.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature missing a modifier
   * @param the_expected expected modifier
   */
  public void logExpectedFeatureModifier(final SourceLocation the_src,
                                         final SmartString a_class,
                                         final SmartString a_feature,
                                         final FeatureModifier the_expected) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "expectedFeatureModifierMsg"), //$NON-NLS-1$
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
  public void logExpectedFeatureModifierWarning(final SourceLocation the_src,
                                                final SmartString a_class,
                                                final SmartString a_feature,
                                                final FeatureModifier the_expected) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "expectedFeatureModifierMsg"), //$NON-NLS-1$
                                      a_class, a_feature,
                                      my_pretty.getFeatMod(the_expected))));
  }

  /**
   * Class is expected to be an enumerated type.
   * @param the_src source location of error
   * @param a_class name of class expected to be enum
   */
  public void logExpectedEnum(final SourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "expectedEnum"), //$NON-NLS-1$
                                      a_class)));
  }

  /**
   * Multiple potential matches found for one class.
   * @param a_class class name with multiple matches
   */
  public void logMultipleClasses(final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, null,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "multiplePotentialMatchesMsg"), //$NON-NLS-1$
                                      a_class)));
  }

  /**
   * A class is not accessible, ie private.
   * @param the_src source location of error
   * @param a_class not accessible class
   */
  public void logNotAccessible(final SourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "privateNotAccessibleMsg"), //$NON-NLS-1$
                                      a_class)));
  }

  /**
   * Class has a redundant enclosing class (aggregation).
   * @param the_src source location of error
   * @param a_class class with redundant enclosing class
   * @param the_found redundant enclosing class
   */
  public void logRedundantEnclosingClass(final SourceLocation the_src,
                                         final SmartString a_class,
                                         final SmartString the_found) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "redundantEnclosingClassMsg"), //$NON-NLS-1$
                                      a_class, the_found)));
  }

  /**
   * Redundant interface.
   * @param the_src source location of error
   * @param a_class class with redundant interface
   * @param a_redundant_cls redundant interface name
   */
  public void logRedundantInterface(final SourceLocation the_src, final SmartString a_class,
                                    final SmartString a_redundant_cls) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "redundantInterfaceMsg"), //$NON-NLS-1$
                                      a_redundant_cls, a_class)));
  }

  /**
   * Redundant constructor.
   * @param the_src source location of error
   * @param the_class class with redundant constructor
   */
  public void logRedundantConstructor(final SourceLocation the_src,
                                      final SmartString the_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "redundantConstructorMsg"), //$NON-NLS-1$
                                      the_class)));
  }

  /**
   * Redundant shared association.
   * @param the_src source location of error
   * @param the_class class with redundant shared association
   * @param the_redundant_ass name of redundant associated class
   */
  public void logRedundantSharedAssociation(final SourceLocation the_src,
                                            final SmartString the_class,
                                            final SmartString the_redundant_ass) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "redundantSharedAssociationMsg"),  //$NON-NLS-1$
                                      the_class, the_redundant_ass)));
  }

  /**
   * Redundant aggregation.
   * @param the_src source location of error
   * @param the_class class with redundant aggregation
   * @param the_redundant_ass name of redundant aggregated class
   */
  public void logRedundantAggregation(final SourceLocation the_src,
                                      final SmartString the_class,
                                      final SmartString the_redundant_ass) {
    if (the_src.isJavaFile()) {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "redundantAggregationMsgJava"), //$NON-NLS-1$
                                        the_class, the_redundant_ass)));
    } else {
      my_records.
      add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                          String.format(Beetlz.getResourceBundle().
                                        getString("CCLogManager." +
                                        "redundantAggregationMsgBon"), //$NON-NLS-1$
                                        the_class, the_redundant_ass)));
    }
  }

  /**
   * Redundant features.
   * @param the_src source location of error
   * @param a_class class with redundant features
   * @param the_features list of redundant features
   */
  public void logRedundantFeature(final SourceLocation the_src, final SmartString a_class,
                                  final List < FeatureStructure > the_features) {
    String list = ""; //$NON-NLS-1$
    final int two = 2;
    for (final FeatureStructure s : the_features) {
      list += s.getSimpleName() + ", "; //$NON-NLS-1$
    }
    if (list.length() > two) list = list.substring(0, list.length() - two);
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "redundantFeaturesMsg"), //$NON-NLS-1$
                                      a_class, list)));
  }

  /**
   * A class should not have a modifier is has.
   * @param the_src source location of error
   * @param a_class class with additional modifier
   * @param a_should_not modifier that should not be present
   */
  public void logShouldNotClassModifier(final SourceLocation the_src,
                                        final SmartString a_class,
                                        final ClassModifier a_should_not) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "shouldNotClassMsg"), //$NON-NLS-1$
                                      a_class, my_pretty.getClassMod(a_should_not))));
  }

  /**
   * A class should not have a modifier is has.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with additional modifier
   * @param a_should_not modifier it should not have
   */
  public void logShouldNotFeatureModifierWarning(final SourceLocation the_src,
                                                 final SmartString a_class,
                                                 final SmartString a_feature,
                                                 final FeatureModifier a_should_not) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "shouldNotFeatureMsg"), //$NON-NLS-1$
                                      a_feature, a_class,
                                      my_pretty.getFeatMod(a_should_not))));
  }

  /**
   * A class should not be an enumerated type.
   * @param the_src source location of error
   * @param a_class name of class that should not be enumerated
   */
  public void logShouldNotEnum(final SourceLocation the_src, final SmartString a_class) {
    my_records.
    add(new CCLogRecord(CCLevel.JAVA_WARNING, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "shouldNotEnum"), //$NON-NLS-1$
                                      a_class)));
  }

  /**
   * A feature has too many parameters.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with too many parameters
   * @param some_params list of additional parameters
   */
  public void logTooManyParameter(final SourceLocation the_src,
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
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "tooManyParameterMsg"), //$NON-NLS-1$
                                      a_feature, a_class, list)));
  }

  /**
   * A feature has too many preconditions.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with too many preconditions
   * @param the_pre list of additional preconditions
   */
  public void logTooManyPrecondition(final SourceLocation the_src,
                                     final SmartString a_class,
                                     final SmartString a_feature,
                                     final List < Expression > the_pre) {
    String clauses = ""; //$NON-NLS-1$
    for (final Expression s : the_pre) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "surplusPreconditionMsg"), //$NON-NLS-1$
                                      a_feature, a_class, clauses)));
  }

  /**
   * A feature has too many postconditions.
   * @param the_src source location of error
   * @param a_class class with fault
   * @param a_feature feature with too many postconditions
   * @param the_post list of additional postconditions
   */
  public void logTooManyPostcondition(final SourceLocation the_src,
                                      final SmartString a_class,
                                      final SmartString a_feature,
                                      final List < Expression > the_post) {
    String clauses = ""; //$NON-NLS-1$
    for (final Expression s : the_post) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "surplusPostconditionMsg"), //$NON-NLS-1$
                                      a_feature, a_class, clauses)));
  }

  /**
   * A class has too many invariants.
   * @param the_src source location of error
   * @param a_class class with too many invariants
   * @param the_inv list of additional invariants
   */
  public void logTooManyInvariant(final SourceLocation the_src, final SmartString a_class,
                                  final List < Expression > the_inv) {
    String clauses = ""; //$NON-NLS-1$
    for (final Expression s : the_inv) {
      if (my_to_bon) {
        clauses += "\n\t" + s.toBonString(); //$NON-NLS-1$
      } else {
        clauses += "\n\t" + s.toJavaString(); //$NON-NLS-1$
      }
    }
    my_records.
    add(new CCLogRecord(CCLevel.JML_ERROR, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "surplusInvariantsMsg"), //$NON-NLS-1$
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
  public void logRedefinedCorrespondence(final SourceLocation the_src,
                                         final SmartString a_class,
                                         final SmartString a_feature) {
    my_records.
    add(new CCLogRecord(CCLevel.GENERAL_NOTE, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "redefinedCorrespondenceMsg"), //$NON-NLS-1$
                                      a_class, a_feature)));
  }

  /**
   * General note about the different defaults for
   * frame conditions.
   */
  public void logAssignableDefaultCorrespondence() {
    my_records.
    add(new CCLogRecord(CCLevel.GENERAL_NOTE, null,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "assignableDefaultMsg")))); //$NON-NLS-1$

  }

  /**
   * General note about the different nullity defaults.
   */
  public void logNullityDefaultCorrespondence() {
    my_records.
    add(new CCLogRecord(CCLevel.GENERAL_NOTE, null,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "nullityDefaultMsg")))); //$NON-NLS-1$
  }

  /**
   * General note that generic methods are not supported.
   * @param the_src source location of error
   * @param the_class class with generic method
   * @param the_method method with generic parameters
   */
  public void logGenericMethodNotSupported(final SourceLocation the_src,
                                           final SmartString the_class,
                                           final SmartString the_method) {
    my_records.
    add(new CCLogRecord(CCLevel.GENERAL_NOTE, the_src,
                        String.format(Beetlz.getResourceBundle().
                                      getString("CCLogManager." +
                                      "genericMethodsNotSupportedMsg"),  //$NON-NLS-1$
                                      the_method, the_class)));
  }

  /**
   * General note about the entirely matching correspondence
   * of history constraints.
   */
  public void logHistoryConstraints() {
    my_records.add(new CCLogRecord(CCLevel.GENERAL_NOTE, null,
                                   Beetlz.getResourceBundle().
                                   getString("CCLogManager." +
                                   "historyConstraintMsg"))); //$NON-NLS-1$
  }
}
