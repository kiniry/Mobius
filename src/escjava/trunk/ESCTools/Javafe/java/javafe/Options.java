package javafe;

import java.util.ArrayList;
import java.io.*;
import java.util.ArrayList;
import java.util.Iterator;

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
    //************************************************************************
    //     Options
    //************************************************************************   
    /**
     * Holds all the non-option arguments.
     */
    public ArrayList inputEntries;  // elements are InputEntry

    /**
     * Option to restrict output to error/caution/warning messages
     * only - no progress or informational output.
     */
    public boolean quiet = false;

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
    
    /** Option holding the current working directory.
     */
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

    //************************************************************************
    //     Constructors
    //************************************************************************   

    public Options() {
        // Everything should be initialized to default values.
        javafe.util.Info.on = false;
    }

 
    //************************************************************************
    //     Routines to process the command-line
    //************************************************************************   

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
    //@ ensures 0 <= \result && \result <= args.length;
    public final void processOptions(String[] args) throws UsageError {
	inputEntries = new ArrayList(args.length);
	processOptionsLoop(args);
    }

    //@ requires \nonnullelements(args);
    //@ ensures 0 <= \result && \result <= args.length;
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
    //@ requires option != null && \nonnullelements(args);
    //@ requires 0 <= offset && offset <= args.length;
    //@ requires option.charAt(0) == '-';
    //@ ensures 0 <= \result && \result <= args.length;
    public int processOption(String option, String[] args, int offset) 
        throws UsageError {
	if (option.equals("-v")) {
	    javafe.util.Info.on = true;
	    return offset;
	} else if (option.equals("-quiet")) {
	    quiet = true;
	    return offset;
	} else if (option.equals("-noCautions")) {
	    noCautions = true;
	    return offset;
	} else if (option.equals("-sourcepath")) {
	    if (offset >= args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    userSourcePath = args[offset];
	    return offset+1;
	} else if (option.equals("-classpath")) {
	    if (offset >= args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    userPath = args[offset];
	    return offset+1;
	} else if (option.equals("-bootclasspath")) {
	    if (offset>=args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    sysPath = args[offset];
	    return offset+1;
	} else if (option.equals("-currentdir")) {
	    if (offset >= args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    currentdir = args[offset];
	    return offset+1;
	} else if (option.equals("-package")) {
	    if (offset>=args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    inputEntries.add(new InputEntry.Package(args[offset]));
	    return offset+1;
	} else if (option.equals("-class")) {
	    if (offset>=args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    inputEntries.add(new InputEntry.Class(args[offset]));
	    return offset+1;
	} else if (option.equals("-dir")) {
	    if (offset>=args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    inputEntries.add(new InputEntry.Dir(args[offset]));
	    return offset+1;
	} else if (option.equals("-file")) {
	    if (offset>=args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    inputEntries.add(new InputEntry.File(args[offset]));
	    return offset+1;
	} else if (option.equals("-list")) {
	    if (offset>=args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    inputEntries.add(new InputEntry.List(args[offset]));
	    return offset+1;
	} else if (option.equals("-f")) {
	    if (offset>=args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    processFileOfArgs(args[offset]);
	    return offset+1;
	} else if (option.equals("-source")) {
            if ((offset >= args.length) ||
                (args[offset].charAt(0) == '-')) {
                throw new UsageError("Option " + option +
                                     " requires one argument indicating Java source version\n" +
                                     "(e.g., \"-source 1.4\")");
            }
            if (args[offset].equals("1.4"))
                assertIsKeyword = true;
            return offset+1;
        } else if (option.equals("-ea") ||
                   option.equals("-enableassertions")) {
	    assertionsEnabled = true;
	    return offset;
        } else if (option.equals("-da") ||
		   option.equals("-disableassertions")) {
	    assertionsEnabled = false;
	    return offset;
	} else if (option.equals("-help")) {
	    issueUsage = true;
	    return offset;
        } else if (option.equals("-testMode")) {
            testMode = true;
            return offset;
	} else if (option.equals("-showErrorLocation")) {
	    showErrorLocation = true;
            return offset;
	} else if (option.equals("-preferSource")) {
	    fileOrigin = PREFER_SOURCE;
	    return offset;
	} else if (option.equals("-preferBinary")) {
	    fileOrigin = PREFER_BINARY;
	    return offset;
	} else if (option.equals("-preferRecent")) {
	    fileOrigin = PREFER_RECENT;
	    return offset;
	} else if (option.equals("-neverBinary")) {
	    fileOrigin = NEVER_BINARY;
	    return offset;
	} else if (option.equals("-neverSource")) {
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

    public void processFileOfArgs(String filename) throws UsageError {
	try {
	    String[] sa = new String[20]; // more than most lines in the file will be, just for efficiency
	    BufferedReader r = new BufferedReader(new FileReader(filename));
	    String s;
	    while ( (s=r.readLine()) != null) {
		sa = Utils.parseLine(s);
		processOptionsLoop(sa);
	    }
	} catch (IOException e) {
	    ErrorSet.error("Failure while reading input arguments from file " +
		filename + ": " + e);
	}
    }
		

    //************************************************************************
    //     Routines to print options and usage
    //************************************************************************   
    
    /**
     * Print our usage message to <code>System.err</code>.
     *
     * @param name the name of the tool whose options we are printing.
     */
    public void usage(String name) {
	System.err.print(name + ": usage: " + name + " options* ");
	System.err.print(showNonOptions());
	System.err.println(" where options include:");
	System.err.print(showOptions(false));
    }
    
    /**
     * @return non-option usage information in a string.
     */
    public String showNonOptions() { return ""; }
    
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
	return showOptionArray(optionData);
    }

    public String showOptionArray(String[][] data) {
    	StringBuffer sb = new StringBuffer();
	for (int i = 0; i < data.length; ++i) {
	    sb.append(format(data[i]));
        }
	return sb.toString();
    }

    public String format(String[] sa) {
	return ("  " + sa[0] + " : " + sa[1] + eol);
    }

    final String[][] optionData = {
    {"-help",                   "Prints a usage message and terminates"},
    {"-v",                      "verbose mode"},
    {"-quiet",                  "quiet mode (no informational messages)"},
    {"-bootclasspath <classpath>", ""},
    {"-classpath <classpath>",  "Directory path for class files (default is value of CLASSPATH)"},
    {"-da, -disableassertions", "Ignores all Java assert statements"},
    {"-ea, -enableassertions",  "Processes all Java assert statements"},
    {"-noCautions",             ""},
    {"-package <packagename>",  "Loads all the files in the named package"},
    {"-source <release>",       "Provide source compatibility with specified release"},
    {"-sourcepath <classpath>", "Directory path for source files (default is classpath)"},
    {"-testMode",               "Replaces execution time by a constant string and path separators by `|' so oracle files can be used in automated testing"},
    };
    
    final public String eol = System.getProperty("line.separator");
}

