package javafe;

import java.io.*;
import java.util.ArrayList;
import java.util.StringTokenizer;

import javafe.util.ErrorSet;
import javafe.util.UsageError;
import junitutils.Utils;

/**
 * This is the super-class of classes that hold the values of
 * command-line options.  The options are separated from the Main
 * class to improve modularity and to allow the options to be reset
 * during a single execution of the main program.  Consequently, none
 * of the options fields should be static.  The program may hold a
 * static instance of an Options object if it wishes.
 *
 * <p> Derived classes should define overriding methods for
 * <ul>
 * <li> {@link #processOption(String, String[], int)},
 * <li> {@link #showNonOptions()},
 * <li> {@link #showOptions(boolean)}
 * </ul>
 */

public class Options
{
  /**
   * Holds all the non-option arguments.
   */
  public ArrayList inputEntries; // elements are InputEntry

  /**
   * Option to restrict output to error/caution/warning messages
   * only - no progress or informational output.
   */
  public boolean quiet = false;
    
  /** 
   * Option to generate lots of output indicating what is happening
   * during execution.
   */
  // public boolean v = false;

  /**
   * When true, no variable output (e.g., execution time) is
   * printed, so that output can be compared to an oracle output
   * file.  Also, emit all paths for warnings, errors, etc. in
   * canonical, machine-independent form.  Such output is strictly
   * used for unit testing.  The canonical form of a path replaces
   * all use of the slash ('/') and wack ('\') characters with bar
   * ('|').
   */
  public boolean testMode = false;

  /**
   * Option to turn off caution warnings.  This is used for Houdini
   * where it is a pain to weed out the cautions from code where we
   * are looking only at warnings.
   */
  public boolean noCautions = false;

  /** Option holding the current working directory. */
  public String currentdir = System.getProperty("user.dir");

  /**
   * Option holding the user-specified classpath.
   */
  public String userPath = null;

  /**
   * Option holding the user-specified sourcepath.
   */
  public String userSourcePath = null;

  /**
   * Option holding the user-specified boot classpath.
   */
  public String sysPath = null;

  /** True if we should simply issue a usage message and abort. */
  public boolean issueUsage = false;

  // Note - the "-v" option is directly set in javafe.util.Info.on

  /**
   * Are we parsing Java 1.4 source code (i.e., we must parse the
   * new "assert" Java keyword).
   *
   * @design As Java evolves we'll likely have to change this to an
   * enumeration type.
   */
  public boolean assertIsKeyword = false;

  /** 
   * Java allows assertions to be enabled and disabled.  Replicate
   * those options as well.
   */
  public boolean assertionsEnabled = false;

  /**
   * Debugging flag used to turn on stack trace dumps when error
   * messages are issued. (cf. javafe.util.ErrorSet)
   */
  public boolean showErrorLocation = false;

  /**
   *	Flags to use or not use source or binary files.
   */
  static public final int PREFER_BINARY = 0;
  static public final int PREFER_SOURCE = 1;
  static public final int PREFER_RECENT = 2;
  static public final int NEVER_BINARY = 3;
  static public final int NEVER_SOURCE = 4;
  public int fileOrigin = PREFER_RECENT;

  public Options() {
    // Everything should be initialized to default values.
    javafe.util.Info.on = false;
  }

  /**
   * Process tool options contained in <code>args</code>.
   *
   * @param args the command-line arguments that are being processed.
   * @return The offset to any remaining command-line arguments
   * should be returned.  (This allows the option to consume some or
   * all of the following arguments.  E.g., this routine "consumes"
   * <code>args[0]</code>, ...,
   * <code>args[</code><i>returned_value</i><code>-1]</code>.)
   * @exception UsageError If the option is erroneous, throw an
   * {@link UsageError} exception with a string describing the
   * problem.
   */
  //@ requires \nonnullelements(args);
  //@ ensures inputEntries != null;
  public final void processOptions(String[] args) throws UsageError {
    inputEntries = new ArrayList(args.length);
    processOptionsLoop(args);
  }

  //@ requires \nonnullelements(args);
  //@ requires inputEntries != null;
  protected final void processOptionsLoop(String[] args) throws UsageError {
    int offset = 0;

    while (offset < args.length) {
      String s = args[offset++];
      if (s.length() == 0) {
        // skip
      } else if (s.charAt(0) == '-') {
        offset = processOption(s, args, offset);
      } else {
        inputEntries.add(new InputEntry.Unknown(s));
      }
    }
  }

  /**
   * Process next tool option.
   *
   * <p> This routine handles the standard front-end options, storing the
   * resulting information in the preceding instance variables and
   * <code>Info.on</code>.
   *
   * @design When this routine is overridden, the new method body should
   * always end with <code>return super.processOption(option, args,
   * offset)</code>.
   *
   * @param option the option currently being handled.  An option
   * always starts with a '-' character, and the remaining
   * command-line arguments (not counting <code>option</code>)
   * (<code>args[offset]</code>,...,<code>args[args.length-1]</code>).
   * @param args the command-line arguments that are being processed.
   * @param offset the offset into the <code>args</args> array that
   * indicates which option is currently being dealt with.
   * @return The offset to any remaining command-line arguments
   * should be returned.  (This allows the option to consume some or
   * all of the following arguments.)
   * @exception UsageError If the option is erroneous, throw an
   * {@link UsageError} exception with a string describing the
   * problem.
   */
  //@ requires option != null;
  //@ requires \nonnullelements(args);
  //@ requires 0 <= offset && offset <= args.length;
  //@ ensures 0 <= \result && \result <= args.length;
  public int processOption(String option, String[] args, int offset)
    throws UsageError {
    option = option.toLowerCase();
    if (option.equals("-v") || 
        option.equals("-verbose")) {
      javafe.util.Info.on = true;
      return offset;
    } else if (option.equals("-q") || 
               option.equals("-quiet")) {
      quiet = true;
      return offset;
    } else if (option.equals("-nocautions")) {
      noCautions = true;
      return offset;
    } else if (option.equals("-sourcepath")) {
      checkMoreArguments(option, args, offset);
      userSourcePath = args[offset];
      return offset + 1;
    } else if (option.equals("-classpath") ||
               option.equals("-cp")) {
      checkMoreArguments(option, args, offset);
      userPath = args[offset];
      return offset + 1;
    } else if (option.equals("-bootclasspath")) {
      checkMoreArguments(option, args, offset);
      sysPath = args[offset];
      return offset + 1;
    } else if (option.equals("-currentdir")) {
      checkMoreArguments(option, args, offset);
      currentdir = args[offset];
      return offset + 1;
    } else if (option.equals("-package")) {
      checkMoreArguments(option, args, offset);
      inputEntries.add(new InputEntry.Package(args[offset]));
      return offset + 1;
    } else if (option.equals("-class")) {
      checkMoreArguments(option, args, offset);
      inputEntries.add(new InputEntry.Class(args[offset]));
      return offset + 1;
    } else if (option.equals("-dir")) {
      checkMoreArguments(option, args, offset);
      inputEntries.add(new InputEntry.Dir(args[offset]));
      return offset + 1;
    } else if (option.equals("-file")) {
      checkMoreArguments(option, args, offset);
      inputEntries.add(new InputEntry.File(args[offset]));
      return offset + 1;
    } else if (option.equals("-list")) {
      checkMoreArguments(option, args, offset);
      inputEntries.add(new InputEntry.List(args[offset]));
      return offset + 1;
    } else if (option.equals("-f")) {
      checkMoreArguments(option, args, offset);
      processFileOfArgs(args[offset]);
      return offset + 1;
    } else if (option.equals("-source")) {
      if ((offset >= args.length) || (args[offset].charAt(0) == '-')) {
        throw new UsageError(
                             "Option "
                             + option
                             + " requires one argument indicating Java source version\n"
                             + "(e.g., \"-source 1.4\")");
      }
      if (args[offset].equals("1.4"))
        assertIsKeyword = true;
      return offset + 1;
    } else if (option.equals("-ea") || 
               option.equals("-enableassertions")) {
      assertionsEnabled = true;
      return offset;
    } else if (option.equals("-da") || 
               option.equals("-disableassertions")) {
      assertionsEnabled = false;
      return offset;
    } else if (option.equals("-h") ||
               option.equals("-help")) {
      issueUsage = true;
      return offset;
    } else if (option.equals("-testmode")) {
      testMode = true;
      return offset;
    } else if (option.equals("-showerrorlocation")) {
      showErrorLocation = true;
      return offset;
    } else if (option.equals("-prefersource")) {
      fileOrigin = PREFER_SOURCE;
      return offset;
    } else if (option.equals("-preferbinary")) {
      fileOrigin = PREFER_BINARY;
      return offset;
    } else if (option.equals("-preferrecent")) {
      fileOrigin = PREFER_RECENT;
      return offset;
    } else if (option.equals("-neverbinary")) {
      fileOrigin = NEVER_BINARY;
      return offset;
    } else if (option.equals("-neversource")) {
      fileOrigin = NEVER_SOURCE;
      return offset;
    } else if (option.equals("--")) {
      while (offset < args.length) {
        inputEntries.add(new InputEntry.Unknown(args[offset++]));
      }
      return offset;
    }

    // Pass on unrecognized options:

    // Derived classes will call:
    // return super.processOption(option, args, offset);

    // Here we inline the error processing	
    throw new UsageError("Unknown option: " + option);
  }

  //@   protected normal_behavior
  //@   requires offset < args.length;
  //@ also protected exceptional_behavior
  //@   requires offset >= args.length;
  //@   signals (Exception e) e instanceof UsageError;
  //@ pure
  protected void checkMoreArguments(String option, String[] args, int offset)
    throws UsageError {
    if (offset >= args.length) {
      throw new UsageError("Option " + option + " requires one argument");
    }
  }

  public void processFileOfArgs(String filename) throws UsageError {
    try {
      String[] sa = new String[20];
      // more than most lines in the file will be, just for efficiency
      BufferedReader r = null;
      try { 
        r = new BufferedReader(new FileReader(filename));
        String s;
        while ((s = r.readLine()) != null) {
          sa = Utils.parseLine(s);
          processOptionsLoop(sa);
        }
      } finally {
        if (r != null) r.close();
      }
    } catch (IOException e) {
      ErrorSet.error(
                     "Failure while reading input arguments from file "
                     + filename
                     + ": "
                     + e);
    }
  }

  /**
   * Print our usage message to <code>System.err</code>.
   *
   * @param name the name of the tool whose options we are printing.
   */
  public void usage(String name) {
    System.err.print(name + ": usage: " + name + " options* ");
    System.err.print(showNonOptions());
    System.err.println(" where options include:");
    System.err.print(showOptions(javafe.util.Info.on));
  }

  /**
   * @return non-option usage information in a string.
   */
  public String showNonOptions() {
    return "All switches are case-insensitive.";
  }

  /**
   * Return option information in a string where each line is
   * preceeded by two blank spaces and followed by a line separator.
   *
   * @param all if true, then all options are printed, including
   * experimental options; otherwise, just the options expected to
   * be used by standard users are printed.
   * @return a String containing all option information ready for
   * output.
   *
   * @usage Each overriding method should first call
   * <code>super.showOptions()</code>.
   */
  public String showOptions(boolean all) {
    String result = showOptionArray(publicOptionData);
    if (all) result += showOptionArray(privateOptionData);
    return result;
  }

  public String showOptionArray(String[][] data) {
    StringBuffer sb = new StringBuffer();
    for (int i = 0; i < data.length; ++i) {
      sb.append(format(data[i]));
    }
    return sb.toString();
  }

  public String format(String[] sa) {
    int columns = Integer.getInteger("COLUMNS", 80).intValue();
    StringBuffer sb = new StringBuffer("  " + sa[0] + " : ");
    int current_column = 2 + sa[0].length() + 3;
    // find the most words that fit into columns-(2 + sa[0].length + 3)
    // for first line.  thereafter, find the most words that fit into
    // (columns-8) lines until there is no remaining words.
    StringTokenizer st = new StringTokenizer(sa[1]);
    while (st.hasMoreTokens()) {
      String word = st.nextToken();
      if (current_column + word.length() < columns) {
        sb.append(word + " ");
        current_column += word.length() + 1;
      }
      else {
        sb.append(eol + "\t" + word + " ");
        current_column = 9 + word.length();
      }
    }
    sb.append(eol);
    return sb.toString();
  }

  final String[][] publicOptionData = {
    { "-Help, -h", 
      "Prints this usage message and terminates (combine with -v to see private\n" + 
      "\tswitches)" }, 
    { "-Verbose, -v", 
      "verbose mode" }, 
    { "-Quiet, -q", 
      "quiet mode (no informational messages)" }, 
    { "-BootClassPath <classpath>",
      "Directory path for specification and class files for the current JDK (default is the built-in classpath of your JDK); prepended to the current classpath" },
    { "-Class <fully.specified.classname>",
      "Check the specified class; this option can be specified multiple times" },
    { "-ClassPath <classpath>, -cp <classpath>",
      "Directory path for class files (default  is value of CLASSPATH) and overrides all previous uses of -classpath." },
    { "-DisableAssertions, -da",
      "Ignores all Java assert statements" },
    { "-dir <directory>",
      "Check all Java files in the specified directory" },
    { "-EnableAssertions, -ea",
      "Processes all Java assert statements" },
    { "-f <file containing command-line arguments>",
      "Path to a file containing command- line arguments that are inserted at this point in the command-line"},
    { "-File <filename>",
      "Check all classes in the specified file <filename>" },
    { "-List <filename>",
      "Check all classes listed in the text file <filename>; each classname in the file should be fully specified and end-of-line terminated" },
    { "-NoCautions", 
      "Does not print messages that are simply cautions" }, 
    { "-Package <packagename>",
      "Loads all the files in the named package" },
    { "-Source <release>",
      "Provide source compatibility with specified release" },
    { "-SourcePath <classpath>",
      "Directory path for source files (default is classpath)" },
  };

  final String[][] privateOptionData = {
    { "-CurrentDir <directory>",
      "Specify the current working directory (REMOVE THIS OPTION?)" },
    { "-TestMode",
      "Replaces execution time by a constant string and path separators by `|'\n" + 
      "so oracle files can be used in automated testing" },
    { "-NeverBinary",
      "Never read type information from a class files" },
    { "-NeverSource",
      "Never read type information from source files" },
    { "-PreferBinary",
      "Read type information from class files even if they are out-of-date" },
    { "-PreferRecent",
      "Read type information from either class or source files, whichever is\n" + 
      "most recent" },
    { "-PreferSource",
      "Read type information from source if it is available, otherwise use\n" + 
      "class files" },
    { "-ShowErrorLocation",
      "Dump a stacktrace to standard error when reporting a warning or error" },
  };

  final static public String eol = System.getProperty("line.separator");
}
