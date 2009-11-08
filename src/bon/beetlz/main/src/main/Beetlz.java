package main;

import input.BonFile;
import input.JmlFile;

import java.io.File;
import java.io.FilenameFilter;
import java.io.IOException;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.util.List;
import java.util.Locale;
import java.util.ResourceBundle;
import java.util.Vector;
import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.StreamHandler;

import log.CCLevel;
import log.CCLogFormatter;
import log.CCLogManager;
import log.CCLogRecord;
import log.ErrorFilter;
import log.OutputFilter;
import pretty.BonPretty;
import pretty.JavaPretty;
import structure.ClassCollection;
import structure.ClassStructure;
import utils.BConst;
import utils.TwoWayMap;
import utils.smart.FeatureSmartString;
import utils.smart.SmartString;
import utils.smart.TypeSmartString;
import check.ClassTranslator;

/**
 * The usage interface of the Consistency Checker.
 * This class is responsible for all organisation.
 * It parses the user's arguments, interprets them,
 * maps class names, and sends them for consistency check,
 * if that is the option.
 * Otherwise, it starts the pretty printing of skeleton code
 * and chooses the correct language.
 * Apart from this, it provides access to log records, compilation
 * errors, resource bundles for localisation and user options.
 * @author Eva Darulova (edarulova@googlemail.com)
 * @version beta-1
 */
public class Beetlz {
  
  /** The id for this (Eclipse) plugin */
  public static final String PLUGIN_ID = "Beetlz";
  /** The path to the built-in jmlspecs for this plugin */
  public static final String JMLSPECS_PATH = "lib/openjml.jar";
  
  /**
   * Filter for BON files.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  private class BONFilter implements FilenameFilter {
	  //TODO: remove BONFilter
    /**
     * Should the file be accepted.
     * @see java.io.FilenameFilter#accept(java.io.File, java.lang.String)
     * @param a_file file to check
     * @param a_file_name file name
     * @return true if file should be accepted
     */
    @Override
    public boolean accept(final File a_file, final String a_file_name) {
      return a_file_name.endsWith(".bon"); //$NON-NLS-1$
    }
  }

  /**
   * Filter for Java files.
   * @author Eva Darulova (edarulova@googlemail.com)
   * @version beta-1
   */
  private class JavaFilter implements FilenameFilter {
	  //TODO: remove JavaFilter
    /**
     * Should the file be accepted.
     * @see java.io.FilenameFilter#accept(java.io.File, java.lang.String)
     * @param a_file file to check
     * @param a_file_name file name
     * @return true if file should be accepted
     */
    @Override
    public boolean accept(final File a_file, final String a_file_name) {
      return a_file_name.endsWith(".java"); //$NON-NLS-1$
    }
  }

  /** Enumeration for status of this tool, maily used for Eclipse plugin. */
  public enum Status {
    /** Status. */
    HELP, OPTIONS_OK, PARSING_OK, PARSING_PROBLEM, STARTED
  }
  
  /** Where to print errors. */
  private static PrintStream errorStream;
  /** Command line option. */
  public static final String HELP_OPTION = "-help"; //$NON-NLS-1$
  /** Our Logger for this session.  */
  public static final Logger JAVA_LOGGER = Logger.getLogger(BConst.LOGGER_NAME);
  /** Localisation bundle. */
  private static ResourceBundle my_labels = ResourceBundle
      .getBundle("BeetlzMsg", new Locale(System.getProperty("user.language"))); //$NON-NLS-1$
  /** Class name mapping. */
  private static TwoWayMap < String, String > my_class_map =
    new TwoWayMap < String, String > ();

  /** Only ever one. */
  private static CCLogManager my_logger;

  /** Command line option. */
  public static final String NO_BASICS_OPTION = "-noBasics"; //$NON-NLS-1$

  /** Command line option. */
  public static final String NO_ERROR_OPTION = "-noError"; //$NON-NLS-1$

  /** Command line option. */
  public static final String NO_JAVA_OPTION = "-noJava"; //$NON-NLS-1$

  /** Command line option. */
  public static final String NO_JML_OPTION = "-noJML"; //$NON-NLS-1$

  /** Command line option. */
  public static final String NO_WARNING_OPTION = "-noWarning"; //$NON-NLS-1$

  /** Command line option. */
  public static final String NON_NULL_OPTION = "-noNullCheck"; //$NON-NLS-1$;

  /** Command line option. */
  public static final String PUREBON_OPTION = "-pureBON"; //$NON-NLS-1$

  /** Storing error messages until we can pass them on to LogManager. */
  private static List < CCLogRecord > my_records_waiting;

  /** Command line option. */
  public static final String SKELETON_ONE_FILE_OPTION = "-skeletonOneFile"; //$NON-NLS-1$

  /** Command line option. */
  public static final String SKELETON_OPTION = "-skeleton"; //$NON-NLS-1$

  /** Command line option. */
  public static final String SOURCE_OPTION = "-source"; //$NON-NLS-1$

  /** Command line option. */
  public static final String SPECS_OPTION = "-specs"; //$NON-NLS-1$

  /** Command line option. */
  public static final String USERSET_OPTION = "-userSettings"; //$NON-NLS-1$

  /** Command line option. */
  public static final String VERBOSE_OPTION = "-verbose"; //$NON-NLS-1$

  /** Command line option. */
  public static final String JAVA_JML_CLASSPATH_OPTION = "-javajmlcp"; //$NON-NLS-1$
  
  /** Configuration settings. */
  private static UserProfile my_profile;

  /**
   * Get the user profile.
   * @return current users settings
   */
  public static final UserProfile getProfile() {
    return my_profile;
  }

  /** BON input. */
  private final BonFile my_bonfile;
  /** Jml and Java input. */
  private final JmlFile my_jmlfile;
  /** Stores the status. */
  private Status my_status;
  /** Command line arguments have been parsed okay.  */
  private boolean my_options_ok;
  /** Files have been parsed okay.  */
  private boolean my_parse_ok;

  /**
   * Create a new Beetlz tool.
   * @param some_args arguments
   * @param an_error_stream errors to print to
   * @param an_out_stream output to print to
   */
  public Beetlz(final String[] some_args, final PrintStream an_error_stream,
                final PrintStream an_out_stream) {

    //***************  Initialisation ***************
    my_status = Status.STARTED;
    errorStream = an_error_stream;
    my_jmlfile = new JmlFile();
    my_bonfile = new BonFile();
    my_records_waiting = new Vector < CCLogRecord > ();

    
    
    //***************  Set up Logger  ***************
    final StreamHandler errorHandler = new StreamHandler(an_error_stream,
                                                         new CCLogFormatter());
    final ErrorFilter errorfilter = new ErrorFilter();
    errorHandler.setLevel(Level.FINEST);
    errorHandler.setFilter(errorfilter);
    JAVA_LOGGER.addHandler(errorHandler);
    JAVA_LOGGER.setUseParentHandlers(false);
    JAVA_LOGGER.setLevel(Level.FINEST);

    
    
    //***************  Parse options ***************
    my_options_ok = true;
    my_profile = processOptions(some_args);
    if (my_profile == null) {
      my_options_ok = false;
      my_status = Status.HELP;
      JAVA_LOGGER.severe(getUsage());
      
      
      
    //*************** Options OK ***************
    } else {
      my_status = Status.OPTIONS_OK;
      if (my_profile.getCustomSettingFile() != null) {
        SettingIO.readSettings(my_profile, my_profile.getCustomSettingFile());
      }
      
      
      
      //*************** Set up rest ***************
      SmartString.setDictionary(my_profile.getBasicDictionary());
      FeatureSmartString.setPrefixes(my_profile.getPrefixes());
      final StreamHandler outputHandler = new StreamHandler(
                                                            an_out_stream,
                                                            new CCLogFormatter());
      final OutputFilter outputfilter = new OutputFilter(!my_profile.noError(),
                                                         !my_profile.noWarning(),
                                                         !my_profile.noJml(),
                                                         !my_profile.noJava(),
                                                         true,
                                                         my_profile.verbose());
      outputHandler.setLevel(Level.FINEST);
      outputHandler.setFilter(outputfilter);
      JAVA_LOGGER.addHandler(outputHandler);

      
      
      //*************** Parse files ***************
      JAVA_LOGGER.config(my_labels.getString("Beetlz.goingToParse")); //$NON-NLS-1$
      if (my_options_ok) {
        my_parse_ok = parseFiles();
        if (my_parse_ok)
          my_status = Status.PARSING_OK;
        else
          my_status = Status.PARSING_PROBLEM;

        my_logger = new CCLogManager();
        my_logger.addRecords(my_records_waiting);
        JAVA_LOGGER.config(my_labels.getString("Beetlz.finishedParsing")); //$NON-NLS-1$
        my_class_map = createClassTypeMapping();
        //Print some parsing info:
        JAVA_LOGGER.config(my_labels.getString("Beetlz.foundJavaTypes") + //$NON-NLS-1$
                           my_jmlfile.getClassCollection().
                           getAccesibleClassTypes());
        JAVA_LOGGER.config(my_labels.getString("Beetlz.foundBONTypes") + //$NON-NLS-1$
                           my_bonfile.getClassCollection().
                           getAccesibleClassTypes());
        JAVA_LOGGER
            .config(my_labels.getString("Beetlz.classMapping") + my_class_map); //$NON-NLS-1$
        JAVA_LOGGER.config(my_profile.toString());
      } else {
        my_parse_ok = false;
        JAVA_LOGGER.severe(my_labels.getString("Beetlz.optionsIncorrent")); //$NON-NLS-1$
      }
    }
  }

  /**
   * Get the status of the tool.
   * @return status
   */
  public Status getStatus() {
    return my_status;
  }

  /**
   * Print information about how to use this application and the options available.
   * @return string representation of usage
   */
  public final String getUsage() {
    final String message =
      my_labels.getString("Beetlz.intro") + "\n" + //$NON-NLS-1$ //$NON-NLS-2$
      my_labels.getString("Beetlz.usage") + //$NON-NLS-1$
      my_labels.getString("Beetlz.autoRecognized") + //$NON-NLS-1$
      my_labels.getString("Beetlz.optionsAre") + //$NON-NLS-1$
      HELP_OPTION + my_labels.getString("Beetlz.printHelp") + //$NON-NLS-1$
      PUREBON_OPTION + my_labels.getString("Beetlz.pureBonDescription") + //$NON-NLS-1$
      SOURCE_OPTION + my_labels.getString("Beetlz.sourceDescription") + //$NON-NLS-1$
      USERSET_OPTION + my_labels.getString("Beetlz.customDescription") + //$NON-NLS-1$
      SKELETON_OPTION + my_labels.getString("Beetlz.skeletonDescription") + //$NON-NLS-1$
      SKELETON_ONE_FILE_OPTION + my_labels
      .getString("Beetlz.skeletonOneFileDescription") + //$NON-NLS-1$
      VERBOSE_OPTION + my_labels.getString("Beetlz.verboseDescription") + //$NON-NLS-1$
      NO_JML_OPTION + my_labels.getString("Beetlz.ignoreJmlDescription") + //$NON-NLS-1$
      NO_JAVA_OPTION + my_labels.getString("Beetlz.ignoreJavaDescription") + //$NON-NLS-1$
      NO_ERROR_OPTION + my_labels.getString("Beetlz.javaErrorsDescription") + //$NON-NLS-1$
      NO_WARNING_OPTION + my_labels.getString("Beetlz.javaWarningDescription") + //$NON-NLS-1$
      NO_BASICS_OPTION + my_labels.getString("Beetlz.basicsDescription") + //$NON-NLS-1$
      NON_NULL_OPTION + my_labels.getString("Beetlz.nullityDescription") + //$NON-NLS-1$
      "\n" + //$NON-NLS-1$
      my_labels.getString("Beetlz.jmlOptionsDescription") + //$NON-NLS-1$
      SPECS_OPTION + my_labels.getString("Beetlz.specsDescription"); //$NON-NLS-1$
    return message;
  }

  /**
   * Gives information whether the files have been parsed properly.
   * This is mainly used for feedback for the Eclipse plugin.
   * @return true if no compile errors occured during parsing
   */
  public boolean parsedOK() {
    return my_parse_ok;
  }

  /**
   * Run the comparison.
   * @return true if successful
   */
  public final boolean run() {
    boolean success = true;
    if (!my_options_ok) {
      success = false;
    } else if (my_parse_ok && my_profile.skeleton()) {
      startPrettyPrint();

    } else if (my_parse_ok) {
      startComparison();
      
      //check the other way?
      if(my_profile.checkBothWays()) {
        my_profile.setSource(false);
        startComparison();
      }
      
      for (final CCLogRecord r : my_logger.getErrors()) {
        JAVA_LOGGER.log(r);
      }
      JAVA_LOGGER.log(CCLevel.GENERAL_NOTE, my_labels
          .getString("Beetlz.generalNotes")); //$NON-NLS-1$
      for (final CCLogRecord r : my_logger
          .getRecords((CCLevel) CCLevel.GENERAL_NOTE)) {
        JAVA_LOGGER.log(r);
      }
      JAVA_LOGGER
          .log(CCLevel.JAVA_ERROR, my_labels.getString("Beetlz.javaErrors")); //$NON-NLS-1$
      for (final CCLogRecord r : my_logger
          .getRecords((CCLevel) CCLevel.JAVA_ERROR)) {
        JAVA_LOGGER.log(r);
      }
      JAVA_LOGGER.log(CCLevel.JAVA_WARNING, my_labels
          .getString("Beetlz.javaWarnings")); //$NON-NLS-1$
      for (final CCLogRecord r : my_logger
          .getRecords((CCLevel) CCLevel.JAVA_WARNING)) {
        JAVA_LOGGER.log(r);
      }
      JAVA_LOGGER.log(CCLevel.JML_ERROR, my_labels.
                      getString("Beetlz.jmlErrors")); //$NON-NLS-1$
      for (final CCLogRecord r : my_logger
          .getRecords((CCLevel) CCLevel.JML_ERROR)) {
        JAVA_LOGGER.log(r);
      }
      JAVA_LOGGER.log(CCLevel.JML_WARNING, my_labels
          .getString("Beetlz.jmlWarnings")); //$NON-NLS-1$
      for (final CCLogRecord r : my_logger
          .getRecords((CCLevel) CCLevel.JML_WARNING)) {
        JAVA_LOGGER.log(r);
      }
      JAVA_LOGGER.info(my_logger.getStats());

    } else {
      JAVA_LOGGER.severe(my_labels.getString("Beetlz.couldNotParse")); //$NON-NLS-1$
      for (final CCLogRecord r : my_records_waiting) {
        JAVA_LOGGER.log(r);
      }
      success = false;
    }

    for (final Handler h : JAVA_LOGGER.getHandlers()) {
      h.flush();
    }
    return success;

  }

  /**
   * Map classes together.
   * @return mapping
   */
  private TwoWayMap < String, String > createClassTypeMapping() {
    final List < TypeSmartString > bonList =
      new Vector < TypeSmartString > (my_bonfile.getClassCollection()
          .getAccesibleClassTypes());
    final List < TypeSmartString > jmlList =
      new Vector < TypeSmartString > (my_jmlfile.getClassCollection().
          getAccesibleClassTypes());
    final List < TypeSmartString > bonMissing = new Vector < TypeSmartString > ();
    final TwoWayMap < String, String > classMap = new TwoWayMap < String, String > ();

    //BON types are unique, so let's map them to Java types
    for (final TypeSmartString bonName : bonList) {
      //check for user mapping first
      final TypeSmartString jName = new TypeSmartString(my_profile
          .getClassMapping(bonName.toString()));
      if (!jName.toString().equals(BConst.NULL_SMARTSTRING)) {
        final int first = jmlList.indexOf(jName);
        final int last = jmlList.lastIndexOf(jName);
        if (first == -1 || first != last) {
          my_logger.logIncorrectMapping(null, bonName.toString());
        } else {
          classMap.put(bonName.toQualifiedString().toString(), jName
              .toQualifiedString().toString());
          //simple types must be recognized in return values
          my_profile.addTypeMapping(bonName.getSimpleName(), jName
              .getSimpleName());
          jmlList.remove(jName);
        }

      } else {
        final int first = jmlList.indexOf(bonName);
        final int last = jmlList.lastIndexOf(bonName);
        if (first == -1) {
          //my_logger.logClassNotFound(bonName.toString());
          bonMissing.add(bonName);
        } else if (first != last) {
          my_logger.logMultipleClasses(bonName);
        } else {
          classMap.put(bonName.toQualifiedString().toString(), jmlList
              .get(first).toQualifiedString().toString());
          my_profile.addTypeMapping(bonName.getSimpleName(), jmlList.get(first)
              .getSimpleName());
          jmlList.remove(jmlList.get(first));
        }
      }
    } //end for

    if (my_profile.javaIsSource()) {
      for (final TypeSmartString s : jmlList) {
        my_logger.logClassNotFound(s);
      }
    } else {
      for (final TypeSmartString s : bonMissing) {
        my_logger.logClassNotFound(s);
      }
    }

    return classMap;
  }

  /**
   *
   * @param a_dir directory
   * @return files
   */
  private List < File > getFilesFromDirectory(final File a_dir) {
    final List < File > returnFiles = new Vector < File > ();
    if (a_dir.isDirectory()) {
      final File[] files = a_dir.listFiles();
      for (final File oneFile : files) {
        returnFiles.addAll(getFilesFromDirectory(oneFile));
      }
      return returnFiles;
    } else {
      returnFiles.add(a_dir);
      return returnFiles;
    }
  }

  /**
   * Parses the Java and BON input files and also sets the
   * checking direction based on the files' timestamp.
   * If the user specifies a direction himself, the timestamps
   * are ignored.
   * @return true if successful
   */
  private boolean parseFiles() {
    my_jmlfile.addFiles(my_profile.getJavaFiles());
    my_bonfile.addFiles(my_profile.getBonFiles());
    //Now find the latest source file:
    if (my_jmlfile.lastModified() > my_bonfile.lastModified()) {
      my_profile.setJavaIsSource(true);
    } else {
      my_profile.setJavaIsSource(false);
    }
    if (my_profile.javaIsSource())
      JAVA_LOGGER.config(my_labels.getString("Beetlz.checkingDirJB")); //$NON-NLS-1$
    else
      JAVA_LOGGER.config("Beetlz.checkingDirBJ"); //$NON-NLS-1$

    return my_jmlfile.parseAll() && my_bonfile.parseAll();
  }

  /**
   * Process the command line options.
   * @param the_args arguments
   * @return true is successful
   */
  private UserProfile processOptions(final String[] the_args) {
    boolean no_error = false;
    boolean no_warning = false;
    boolean no_java = false;
    boolean no_jml = false;
    boolean verbose = false;
    String source = null;
    boolean check_both = false;
    boolean pure_bon = false;
    boolean no_basics = true;
    boolean skeleton = false;
    String skel_dir = null;
    boolean skel_one_file = false;
    String specs = null;
    boolean check_null = true;
    final List < String > javaFiles = new Vector < String > ();
    final List < String > bonFiles = new Vector < String > ();
    String custom_file = null;
    String classpath = null;

    int i = 0;
    String arg;
    boolean cont = true;
    while (i < the_args.length && the_args[i].startsWith("-") && cont) { //$NON-NLS-1$
      arg = the_args[i++];

      if (arg.equals(HELP_OPTION)) {
        return null;
      } else if (arg.equals(VERBOSE_OPTION)) {
        verbose = true;
      } else if (arg.equals(PUREBON_OPTION)) {
        pure_bon = true;
      } else if (arg.equals(NO_ERROR_OPTION)) {
        no_error = true;
      } else if (arg.equals(NO_WARNING_OPTION)) {
        no_warning = true;
      } else if (arg.equals(NO_JML_OPTION)) {
        no_jml = true;
      } else if (arg.equals(NO_JAVA_OPTION)) {
        no_java = true;
      } else if (arg.equals(NO_BASICS_OPTION)) {
        no_basics = true;
      } else if (arg.equals(NON_NULL_OPTION)) {
        check_null = false;
      } else if (arg.equals(SKELETON_ONE_FILE_OPTION)) {
        skel_one_file = true;
      } else if (arg.equals(SOURCE_OPTION)) {
        if (i < the_args.length) {
          source = the_args[i++];
          if (source == "both") { //$NON-NLS-1$
            check_both = true;
        	source = "java";//$NON-NLS-1$
          }
        } else {
          JAVA_LOGGER.severe(my_labels.getString("Beetlz.sourceNeedsArgument")); //$NON-NLS-1$
          return null;
        }
      } else if (arg.equals(SPECS_OPTION)) {
        if (i < the_args.length) {
          specs = the_args[i++];
        } else {
          JAVA_LOGGER.severe(my_labels.getString("Beetlz.specsNeedsArgument")); //$NON-NLS-1$
          return null;
        }
      } else if (arg.equals(JAVA_JML_CLASSPATH_OPTION)) {
        if (i < the_args.length) {
          classpath = the_args[i++];
        } else {
          JAVA_LOGGER.severe(my_labels.getString("Beetlz.classpathNeedsArgument")); //$NON-NLS-1$
          return null;
        }
      } else if (arg.equals(SKELETON_OPTION)) {
        if (i < the_args.length && !the_args[i].startsWith("-")) { //$NON-NLS-1$
          skel_dir = the_args[i++];
          skeleton = true;
        } else {
          skeleton = true;
        }
      } else if (arg.equals(USERSET_OPTION)) {
        if (i < the_args.length) {
          custom_file = the_args[i++];
        } else {
          JAVA_LOGGER.severe(my_labels.getString("Beetlz.userNeedsArgument")); //$NON-NLS-1$
          return null;
        }
      } else if (arg.equals("-files")) { //$NON-NLS-1$
        cont = false;
      } else {
        JAVA_LOGGER.severe(my_labels.getString("Beetlz.unknownOption") + arg); //$NON-NLS-1$
      }

    } //end while

    if (cont) {
      JAVA_LOGGER.severe(my_labels.getString("Beetlz.mustSpecifyFiles")); //$NON-NLS-1$
      return null;
    }
    final JavaFilter jfilter = new JavaFilter();
    final BONFilter bfilter = new BONFilter();
    for (int j = i; j < the_args.length; j++) {
      final String s = the_args[j];
      if (s.endsWith(".txt")) { //$NON-NLS-1$
        bonFiles.add(s);
      } else {
        final File f = new File(s);
        final List < File > allfiles = getFilesFromDirectory(f);
        for (final File onefile : allfiles) {
          if (jfilter.accept(null, onefile.getAbsolutePath())) {
            javaFiles.add(onefile.getAbsolutePath());
          } else if (bfilter.accept(null, onefile.getAbsolutePath())) {
            bonFiles.add(onefile.getAbsolutePath());
          }
        }
      }

    } //end for

    final UserProfile profile = new UserProfile(no_error, no_warning, no_jml,
                                                no_java, verbose, source, check_both,
                                                pure_bon, skeleton, skel_dir,
                                                skel_one_file, check_null,
                                                javaFiles, bonFiles,
                                                custom_file, no_basics, specs,
                                                classpath);
    return profile;

  }

  /* ****************************
   * Private methods
   ******************************/
  /**
   * Here we do the actual comparison.
   */
  private void startComparison() {
    final ClassCollection jml = my_jmlfile.getClassCollection();
    final ClassCollection bon = my_bonfile.getClassCollection();

    final ClassTranslator checker = new ClassTranslator(my_logger, my_profile);

    ClassCollection source;
    ClassCollection target;
    if (my_profile.javaIsSource()) {
      JAVA_LOGGER.info(my_labels.getString("Beetlz.checkingDirJB")); //$NON-NLS-1$
      source = jml;
      target = bon;
    } else {
      JAVA_LOGGER.info(my_labels.getString("Beetlz.checkingDirBJ")); //$NON-NLS-1$
      source = bon;
      target = jml;
    }
    for (final ClassStructure sourceClass : source.getClasses()) {
      final String targetName = (String) my_class_map.get(sourceClass
          .getQualifiedName().toString());

      if (targetName != null) {
        final ClassStructure targetClass = target.getClass(targetName);
        if (targetClass != null) {
          if (targetClass.isPrivate()) {
            my_logger.logNotAccessible(targetClass.getSourceLocation(),
                                       targetClass.getQualifiedName());
          } else {
            if (my_profile.verbose())
              JAVA_LOGGER
                  .config(my_labels.getString("Beetlz.comparing") + //$NON-NLS-1$
                          sourceClass.getSimpleName() + " " + //$NON-NLS-1$
                          targetClass.getSimpleName());
            checker.doCheck(sourceClass, targetClass);
          }
        } else {
          my_logger.logIncorrectMapping(null, sourceClass.toString());
        }
      }
    }
  }

  /**
   * Start pretty printing.
   */
  private void startPrettyPrint() {
    if (my_profile.getSkeletonDirectory() == null) { //print to std out
      if (my_profile.javaIsSource()) {
        final BonPretty pretty = new BonPretty(BConst.TAB);
        final OutputStreamWriter out = new OutputStreamWriter(System.out);
        pretty.printClassCollection(my_jmlfile.getClassCollection(), out);
        try {
          out.flush();
        } catch (final IOException e) {
          JAVA_LOGGER.severe(my_labels.getString("Beetlz.ioProblem"));
        }
      } else {
        final JavaPretty pretty = new JavaPretty(BConst.TAB);
        final OutputStreamWriter out = new OutputStreamWriter(System.out);
        pretty.printClassCollection(my_bonfile.getClassCollection(), out);
      }
    } else {
      if (my_profile.javaIsSource()) {
        final BonPretty pretty = new BonPretty(BConst.TAB);
        pretty.printToFiles(my_profile.getSkeletonDirectory(), my_jmlfile
            .getClassCollection());
      } else {
        final JavaPretty pretty = new JavaPretty(BConst.TAB);
        pretty.printToFiles(my_profile.getSkeletonDirectory(), my_bonfile
            .getClassCollection());
      }
    }
  }

  /**
   * Get the error stream.
   * @return stream where to print errors
   */
  public static PrintStream getErrorStream() {
    return errorStream;
  }

  /**
   * Get the logger with consistency checking results.
   * @return logger
   */
  public static CCLogManager getLogManager() {
    return my_logger;
  }

  /**
   * Get the localisation resource bundle.
   * @return resource bundle with current locale
   */
  public static ResourceBundle getResourceBundle() {
    return my_labels;
  }

  /**
   * Get the class name mappings.
   * @return class map
   */
  public static TwoWayMap < String, String > getClassMap() {
    return my_class_map;
  }

  /**
   * Get records that have been recorded before logger was set up.
   * @return waiting records
   */
  public static List < CCLogRecord > getWaitingRecords() {
    return my_records_waiting;
  }
}
