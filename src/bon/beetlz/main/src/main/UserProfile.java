package main;

import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;
import java.util.Vector;
import java.util.logging.Logger;

import utils.BConst;
import utils.BasicTypesDictionary;

/**
 * A container for all user defined options.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class UserProfile {
  /** Store input options about what we should print. */
  private final boolean my_no_error;

  /** Store input options about what we should print. */
  private final boolean my_no_warning;

  /** Store input options about what we should print.  */
  private final boolean my_no_jml;

  /** Store input options about what we should print.  */
  private final boolean my_no_java;

  /** Print debug info? */
  private final boolean my_verbose;

  /** Java files source files? */
  private boolean my_java_is_source;
  
  /** Run check both ways? */
  private boolean my_check_both_ways;
  
  /** Stores the original input by the user. */
  private final String my_original_source;

  /** Do we use unextended BON? Main difference is use of constructors. */
  private final boolean my_pure_bon;

  /** Print skeleton code. */
  private final boolean my_skeleton;

  /** Dir for skeleton code. */
  private final String my_skeleton_directory;

  /** Print to one file. */
  private final boolean my_skeleton_one_file;

  /** Custom specs directory. */
  private final String my_specs;
  
  /** The Java/JML classpath, to be passed to openjml. */
  private final String my_classpath;

  /** Check for nullity? */
  private final boolean my_nullity;

  /** Java input files. */
  private final List < String > my_java_files;

  /** BON input files. */
  private final List < String > my_bon_files;

  /** File name of the iser settings customize file. */
  private final String my_custom_setting_file;

  /** Basic BON and Java types.  */
  private final BasicTypesDictionary my_basic_dictionary;

  /** Basic methods for assertion language. */
  private final BasicTypesDictionary my_assertion_dictionary;

  /** Stores equivalent BON and Java class names.  */
  private final SortedSet < MappingPair > my_class_map;

  /** Stores equivalent BON and Java feature/method names. */
  private final SortedSet < FeatureMappingPair > my_feature_map;

  /** Stores equivalent BON and Java feature/method names. */
  private final SortedSet < FeatureMappingPair > my_simple_feature_map;

  /** BON classes to be ignored. */
  private final SortedSet < String > my_ignore_bon;

  /** Java classes to be ignored. */
  private final SortedSet < String > my_ignore_java;

  /** Prefixes of features to be ignored. */
  private final List < String > my_prefixes;

  /**
   * Creates a new user profile.
   * @param a_no_error print errors?
   * @param a_no_warning print warnings?
   * @param a_no_jml print JML errors and warnings?
   * @param a_no_java print Java errors and warnings?
   * @param a_verbose print debug info
   * @param the_source what is the source? value 'bon' or 'java'
   * @param a_pure_bon pure, unextended BON?
   * @param a_skeleton print skeleton code
   * @param the_skeleton_dir where to print skeleton code
   * @param a_skeleton_one_file print to one file
   * @param a_check_null check for nullity
   * @param some_javafiles java/jml input files
   * @param some_bonfiles bon input files
   * @param a_custom_file custom settings file
   * @param a_use_basics use basic_settings file to basic type dictionary?
   * @param the_specs where are the specs
   */
  public UserProfile(final boolean a_no_error, final boolean a_no_warning,
                     final boolean a_no_jml, final boolean a_no_java,
                     final boolean a_verbose, final String the_source,
                     final boolean a_check_both_ways,
                     final boolean a_pure_bon, final boolean a_skeleton,
                     final/*@ nullable @*/String the_skeleton_dir,
                     final boolean a_skeleton_one_file, final boolean a_check_null,
                     final List < String > some_javafiles,
                     final List < String > some_bonfiles,
                     final String a_custom_file, final boolean a_use_basics,
                     final String the_specs, final String the_classpath) {
    my_no_error = a_no_error;
    my_no_warning = a_no_warning;
    my_no_jml = a_no_jml;
    my_no_java = a_no_java;
    my_verbose = a_verbose;
    my_pure_bon = a_pure_bon;
    my_original_source = the_source;
    my_skeleton = a_skeleton;
    my_skeleton_directory = the_skeleton_dir;
    my_skeleton_one_file = a_skeleton_one_file;
    my_specs = the_specs;
    my_classpath = the_classpath;
    my_nullity = a_check_null;
    my_java_files = some_javafiles;
    my_bon_files = some_bonfiles;
    my_custom_setting_file = a_custom_file;
    my_basic_dictionary = new BasicTypesDictionary();
    my_assertion_dictionary = new BasicTypesDictionary();
    my_class_map = new TreeSet < MappingPair > ();
    my_feature_map = new TreeSet < FeatureMappingPair > ();
    my_simple_feature_map = new TreeSet < FeatureMappingPair > ();
    my_ignore_bon = new TreeSet < String > ();
    my_ignore_java = new TreeSet < String > ();
    my_prefixes = new Vector < String > ();
    my_check_both_ways = a_check_both_ways;
    
    if (the_source == null) {
      my_java_is_source = false;
    } else if (the_source.equals("bon")) { //$NON-NLS-1$
      my_java_is_source = false;
    } else if (the_source.equals("java")) { //$NON-NLS-1$
      my_java_is_source = true;
    } else {
      Logger.getLogger(BConst.LOGGER_NAME)
          .severe("Options syntax error: '-source' must be followed " + //$NON-NLS-1$
          		"by either 'bon' or 'java' or 'both'."); //$NON-NLS-1$
      my_java_is_source = false;
    }
    if (a_use_basics) {
      addBasics();
    }

  }

  /**
   * Get the cprresponding mapping.
   * @param a_feature_name original name of feature
   * @param a_src_class class of original feature
   * @param a_trg_class target class of feature mapping
   * @return feature mapping
   */
  public final String getFeatureMapping(final String a_feature_name,
                                  final String a_src_class,
                                  final String a_trg_class) {
    final String src = a_feature_name + "@" + a_src_class; //$NON-NLS-1$
    for (final FeatureMappingPair m : my_feature_map) {
      if (m.my_first.equals(src)) {
        if (m.my_second.contains(a_trg_class)) {
          final int index = m.my_second.lastIndexOf('@');
          if (index != -1 && index != m.my_second.length()) {
            return m.my_second.substring(0, index);
          }
          return m.my_second;
        }
      }
      if (m.my_second.equals(src)) {
        if (m.my_first.contains(a_trg_class)) {
          final int index = m.my_first.lastIndexOf('@');
          if (index != -1 && index != m.my_first.length()) {
            return m.my_first.substring(0, index);
          }
          return m.my_first;
        }
      }
    }
    return null;
  }

  /**
   * Get a feature mapping only by name, not class.
   * @param a_feature_name feature name
   * @return mapping
   */
  public String getSimpleFeatureMapping(final String a_feature_name) {
    for (final FeatureMappingPair m : my_feature_map) {
      if (m.my_first.startsWith(a_feature_name)) {
        return m.my_second.substring(0, m.my_second.indexOf("@")); //$NON-NLS-1$
      }
      if (m.my_second.startsWith(a_feature_name)) {
        return m.my_first.substring(0, m.my_first.indexOf("@")); //$NON-NLS-1$
      }
    }
    for (final FeatureMappingPair m : my_simple_feature_map) {
      if (m.my_first.equals(a_feature_name)) {
        return m.my_second;
      }
      if (m.my_second.equals(a_feature_name)) {
        return m.my_first;
      }
    }
    return null;
  }

  /**
   * Get class mapping.
   * @param a_class_name class name
   * @return mapping
   */
  public String getClassMapping(final String a_class_name) {
    for (final MappingPair m : my_class_map) {
      if (m.my_first.equals(a_class_name)) {
        return m.my_second;
      }
      if (m.my_second.equals(a_class_name)) {
        return m.my_first;
      }
    }
    return null;
  }

  /**
   * Is this class on the Bon ignore list.
   * @param the_class_name class name
   * @return true if is ignored
   */
  public boolean isBONIgnored(final String the_class_name) {
    return my_ignore_bon.contains(the_class_name);
  }

  /**
   * Is this class on the Java ignore list.
   * @param the_class_name class name
   * @return true if is ignored
   */
  public boolean isJavaIgnored(final String the_class_name) {
    return my_ignore_java.contains(the_class_name);
  }

  /**
   * Can set the source input, but only if the user has not
   * done so yet. If a souce has already been specified, this
   * method call has no effect.
   * @param a_java_source true then java is the source input.
   */
  protected void setJavaIsSource(final boolean a_java_source) {
    if (my_original_source == null) {
      my_java_is_source = a_java_source;
    }
  }

  /**
   * Add a class mapping.
   * @param a_bon_name BON name of the mapping
   * @param a_java_name Java name of the mapping
   */
  protected void addClassMapping(final String a_bon_name, final String a_java_name) {
    my_class_map.add(new MappingPair(a_bon_name, a_java_name));
  }

  /**
   * Add a feature mapping.
   * @param a_bon_name BON name of the mapping
   * @param a_java_name Java name of the mapping
   */
  protected void addFeatureMapping(final String a_bon_name,
                                   final String a_java_name) {
    my_feature_map.add(new FeatureMappingPair(a_bon_name, a_java_name));
  }

  /**
   * Add a feature mapping without class information.
   * @param a_bon_name bon part
   * @param a_java_name java part
   */
  protected void addSimpleFeatureMapping(final String a_bon_name,
                                         final String a_java_name) {
    my_simple_feature_map.add(new FeatureMappingPair(a_bon_name, a_java_name));
  }

  /**
   * Add a type mapping.
   * @param a_mapping_name name of this mapping (unique identifier)
   * @param some_bon_types BON types
   * @param some_java_types Java types
   */
  protected void addTypeMapping(final String a_mapping_name,
                                final String[] some_bon_types,
                                final String[] some_java_types) {
    my_basic_dictionary.addMapping(a_mapping_name, some_bon_types, some_java_types);
  }

  /**
   * Add a type mapping.
   * @param a_bon_type BON types
   * @param a_java_type Java types
   */
  protected void addTypeMapping(final String a_bon_type, final String a_java_type) {
    my_basic_dictionary.addMapping(a_bon_type, new String[] {a_bon_type},
                               new String[] {a_java_type});
  }

  /**
   * Add an ignored classes clause.
   * @param some_bon bon ignored classes
   * @param some_java java ignored classes
   */
  protected void addIgnoredClasses(final String[] some_bon,
                                   final String[] some_java) {
    for (final String s : some_bon) {
      my_ignore_bon.add(s.trim());
    }
    for (final String s : some_java) {
      my_ignore_java.add(s.trim());
    }
  }

  /**
   * Pretty print contents.
   * @see java.lang.Object#toString()
   * @return string representation of this user profile
   */
  @Override
  public String toString() {
    String string = "OPTIONS:\n"; //$NON-NLS-1$
    string += "noError: " + my_no_error + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "noWarning: " + my_no_warning + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "noJML: " + my_no_jml + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "verbose: " + my_verbose + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "pureBON: " + my_pure_bon + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "custom setting files: " + my_custom_setting_file +
              "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "Java input files: "; //$NON-NLS-1$
    for (final String s : my_java_files) {
      string += s + "\n"; //$NON-NLS-1$
    }
    string += "BON input files: "; //$NON-NLS-1$
    for (final String s : my_bon_files) {
      string += s + "\n"; //$NON-NLS-1$
    }
    string += "ignored Java files: " + my_ignore_java + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "ignored BON files: " + my_ignore_bon + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "ignored prefixes:" + my_prefixes + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "Basic types dictionary: " + my_basic_dictionary.toString() +
              "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "Class map: " + my_class_map.toString() + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
              "Feature map: " + my_feature_map.toString() + "\n"; //$NON-NLS-1$ //$NON-NLS-2$
    return string;
  }

  /* ****************************
   * Private methods.
   ******************************/

  /**
   * Create type mappings for the very basic types.
   */
  private void addBasics() {
    BasicSettings.doStuff(this);
    BasicSettings.doAssertionStuff(my_assertion_dictionary);
  }

  /**
   * A pair of string for a mapping.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  private class MappingPair implements Comparable < MappingPair > {
    /**  */
    String my_first;
    /** */
    String my_second;

    /**
     * Create new mapping.
     * @param a_one first part
     * @param a_two second part
     */
    MappingPair(final String a_one, final String a_two) {
      if (a_one.compareTo(a_two) < 0) {
        my_first = a_one;
        my_second = a_two;
      } else {
        my_first = a_two;
        my_second = a_one;
      }
    }

    /**
     * Compare two mappings.
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     * @param an_other mapping to compare to
     * @return 0 if equal
     */
    @Override
    public int compareTo(final MappingPair an_other) {
      if (my_first.compareTo(an_other.my_first) == 0) {
        return my_second.compareTo(an_other.my_second);
      } else {
        return my_first.compareTo(an_other.my_first);
      }

    }

    /**
     * Print string.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_first + "-" + my_second; //$NON-NLS-1$
    }
  }

  /**
   * Feature mapping pair.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  private class FeatureMappingPair implements Comparable < FeatureMappingPair > {
    /**  */
    final String my_first;
    /** */
    final String my_second;

    /**
     * Create new mapping.
     * @param a_one first part
     * @param a_two second part
     */
    FeatureMappingPair(final String a_one, final String a_two) {
      if (a_one.compareTo(a_two) < 0) {
        my_first = a_one;
        my_second = a_two;
      } else {
        my_first = a_two;
        my_second = a_one;
      }
    }

    /**
     * Compare two mappings.
     * @see java.lang.Comparable#compareTo(java.lang.Object)
     * @param an_other mapping to compare to
     * @return 0 if equal
     */
    @Override
    public int compareTo(final FeatureMappingPair an_other) {
      if (my_first.compareTo(an_other.my_first) == 0) {
        return my_second.compareTo(an_other.my_second);
      } else {
        return my_first.compareTo(an_other.my_first);
      }

    }

    /**
     * Print string.
     * @see java.lang.Object#toString()
     * @return string representation
     */
    @Override
    public String toString() {
      return my_first + "-" + my_second; //$NON-NLS-1$
    }
  }

  /**
   * Do not print errors.
   * @return true if ignore errors.
   */
  public final boolean noError() {
    return my_no_error;
  }

  /**
   * Do not print warnings.
   * @return true if ignore warnings
   */
  public final boolean noWarning() {
    return my_no_warning;
  }

  /**
   * Do not print JML related errors and ignore
   * JML constructs.
   * @return true if ignore JML
   */
  public final boolean noJml() {
    return my_no_jml;
  }

  /**
   * Do not print Java only related errors.
   * @return true if ignore Java
   */
  public final boolean noJava() {
    return my_no_java;
  }

  /**
   * Print verbose messages.
   * @return true then print debug info
   */
  public final boolean verbose() {
    return my_verbose;
  }

  /**
   * Is Java the source.
   * @return true if Java is source
   */
  public final boolean javaIsSource() {
    return my_java_is_source;
  }
  
  
  /**
   * Do we perform check both ways.
   * @return true if check is to be done both ways
   */
  public final boolean checkBothWays() {
    return my_check_both_ways;
  }

  /**
   * Get the original source ie source given by user
   * or none if none given.
   * @return original source
   */
  public final String getOriginalSource() {
    return my_original_source;
  }

  /**
   * Use pure BON.
   * @return true then ignore all extended BON elements
   */
  public final boolean pureBon() {
    return my_pure_bon;
  }

  /**
   * Generate skeleton code.
   * @return true if skeleton to be printed
   */
  public final boolean skeleton() {
    return my_skeleton;
  }

  /**
   * Get the directory where to put skeleton code.
   * @return skeleton code directory path
   */
  public final String getSkeletonDirectory() {
    return my_skeleton_directory;
  }

  /**
   * Print skeleton code to one file.
   * @return true if printing into one file
   */
  public final boolean skeletonOneFile() {
    return my_skeleton_one_file;
  }

  /**
   * Get path to JML specs.
   * @return specs path
   */
  public final String getSpecs() {
    return my_specs;
  }

  /**
   * Check for nullity.
   * @return true then nullity checks are done
   */
  public final boolean nullity() {
    return my_nullity;
  }

  /**
   * Get Java input file paths.
   * @return java files
   */
  public final List < String > getJavaFiles() {
    return my_java_files;
  }

  /**
   * Get all BON file paths.
   * @return bon files
   */
  public final List < String > getBonFiles() {
    return my_bon_files;
  }

  /**
   * Get path to custom settings file, if present.
   * @return path to settings file
   */
  public final String getCustomSettingFile() {
    return my_custom_setting_file;
  }

  /**
   * Get basic dictionary.
   * @return basic dictionary
   */
  public final BasicTypesDictionary getBasicDictionary() {
    return my_basic_dictionary;
  }

  /**
   * Get dictionary of assertion language elements.
   * @return assertion dictionary
   */
  public final BasicTypesDictionary getAssertionDictionary() {
    return my_assertion_dictionary;
  }

  /**
   * Get class mappings.
   * @return class map
   */
  public final SortedSet < MappingPair > getClassMap() {
    return my_class_map;
  }

  /**
   * Get feature name mappings.
   * @return feature map
   */
  public final SortedSet < FeatureMappingPair > getFeatureMap() {
    return my_feature_map;
  }

  /**
   * Get simple feature name mappings, without class reference.
   * @return simple feature map
   */
  public final SortedSet < FeatureMappingPair > getSimpleFeatureMap() {
    return my_simple_feature_map;
  }

  /**
   * Ignored BON classes.
   * @return ignored BON classes
   */
  public final SortedSet < String > getIgnoreBon() {
    return my_ignore_bon;
  }

  /**
   * Ignored Java classes.
   * @return ignored Java classes
   */
  public final SortedSet < String > getIgnoreJava() {
    return my_ignore_java;
  }

  /**
   * Get ignored prefixes.
   * @return prefixes
   */
  public final List < String > getPrefixes() {
    return my_prefixes;
  }
  
  /**
   * Get the Java/JML classpath.
   * @return the classpath
   */
  public String getClasspath() {
    return my_classpath;
  }

  /**
   * Set source.
   * @param my_java_is_source true, then Java is source
   */
  public final void setSource(boolean my_java_is_source) {
    this.my_java_is_source = my_java_is_source;
  }
}
