package javafe;
import javafe.util.UsageError;
import java.util.ArrayList;

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
 * <li> {@link #showOptions(boolean)},
 * <li> as well as a constructor {@link Options(String[] args)}.
 * </ul>
 */
  
public class Options
{
    //************************************************************************
    //     Options
    //************************************************************************   
    /**
     * Option to restrict output to error/caution/warning messages
     * only - no progress or informational output.
     */
    public boolean quiet = false;

    /**
     * Option to turn off caution warnings.  This is used for Houdini
     * where it is a pain to weed out the cautions from code where we
     * are looking only at warnings.
     */
    public boolean noCautions = false;
    
    /**
     * Option holding the user-specified classpath.
     */
    public String userPath = null;
    
    /**
     * Option holding the user-specified boot classpath.
     */
    public String sysPath = null;
    
    // Note - the "-v" option is directly set in javafe.util.Info.on
    
    /** 
     * Option holding a list of packages to be processed along with
     * files.
     */
    //*@ invariant (* elements have type java.lang.String *)
    public ArrayList packagesToProcess = new ArrayList();

    /**
     * Are we parsing Java 1.4 source code (i.e., we must parse the
     * new "assert" Java keyword).
     *
     * @design As Java evolves we'll likely have to change this to an
     * enumeration type.
     */
    public boolean assertIsKeyword = false;


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
    public final int processOptions(String[] args) throws UsageError {
	int offset = 0;

	while (offset<args.length && args[offset].length()>0 &&
		args[offset].charAt(0)=='-') {
	    offset = processOption(args[offset], args, offset+1);
	}

	return offset;
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
	} else if (option.equals("-package")) {
	    if (offset>=args.length) {
		throw new UsageError("Option " + option + 
                                     " requires one argument");
	    }
	    packagesToProcess.add(args[offset]);
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
        }

	// Pass on unrecognized options:
	
	// Derived classes will call:
	// return super.processOption(option, args, offset);

	// Here we inline the error processing	
        throw new UsageError("Unknown option: " + option);
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
    	StringBuffer sb = new StringBuffer();
	for (int i = 0; i < optionData.length; ++i) {
	    sb.append(format(optionData[i]));
        }
	return sb.toString();
    }

    public String format(String[] sa) {
	return ("  " + sa[0] + " : " + sa[1] + eol);
    }

    final String[][] optionData = {
    {"-v", ""},
    {"-quiet", ""},
    {"-bootclasspath <classpath>", ""},
    {"-classpath <classpath>", ""},
    {"-noCautions", ""},
    {"-package <packagename>", "Loads all the files in the named package"},
    {"-source <release>", "Provide source compatibility with specified release"},
    };
    
    final public String eol = System.getProperty("line.separator");
}

