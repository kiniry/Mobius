package javafe;
import javafe.util.UsageError;

/** This is the super-class of classes that hold the values of command-line
  * options.  The options are separated from the Main class to improve
  * modularity and to allow the options to be reset during a single execution
  * of the main program.  Consequently, none of the options fields should be static.
  * The program may hold a static instance of an Options object if it wishes.
  * <p>
  * Derived classes should define overriding methods for
  *	processOption
  *	showNonOptions
  *	showOptions
  *  as well as a constructor Options(String[] args)
  *	
  */
  
public class Options {
 
    //************************************************************************
    //     Options
    //************************************************************************   
    /**
     * Option to restrict output to error/caution/warning messages only -
     * no progress or informational output.
     */
    public boolean quiet = false;

    /**
     * option to turn off caution warnings.  This is used for 
     * houdini where it is a pain to weed out the cautions from
     * code where we are looking only at warnings.
     */
    public boolean noCautions = false;
    
    /** Option holding the user-specified class path
     */
    public String userPath = null;
    
    /** Option holding the user-specified boot class path
     */
    public String sysPath = null;
    
    // Note - the "-v" option is directly set in javafe.util.Info.on
    

    //************************************************************************
    //     Constructors
    //************************************************************************   

    public Options() {
        // Everything should be initialized to default values
        javafe.util.Info.on = false;
    }

 
    //************************************************************************
    //     Routines to process the command-line
    //************************************************************************   

    /**
     * Process tool options contained in <code>args</code>. <p>
     *
     * If an error occurs, a UsageError exception is thrown
     * Otherwise, the offset to the first non-option in
     * <code>args</code> is returned.  E.g., this routine
     * "consumes" <code>args[0]</code>, ...,
     * <code>args[</code><i>returned_value</i><code>-1]</code>.<p>
     */
    //@ requires \nonnullelements(args)
    //@ ensures 0<=\result && \result<=args.length
    public final int processOptions(String[] args) throws UsageError {
	int offset = 0;

	while (offset<args.length && args[offset].length()>0 &&
		args[offset].charAt(0)=='-') {
	    offset = processOption(args[offset], args, offset+1);
	}

	return offset;
    }

    /**
     * Process next tool option. <p>
     *
     * This routine handles the standard front-end options, storing the
     * resulting information in the preceding instance variables and
     * <code>Info.on</code>.<p>
     *
     * This routine handles processing the next option from the
     * command-line arguments.  It is passed the option in question
     * (<code>option</code>), which will always start with a '-'
     * character, and the remaining command-line arguments (not
     * counting <code>option</code>)
     * (<code>args[offset]</code>,...,<code>args[args.length-1]</code>).<p>
     *
     * If the option is erroneous, throw an UsageError exception with a
     * string describing the problem.  Otherwise, the offset to
     * any remaining command-line arguments should be returned.  (This
     * allows the option to consume some or all of the following
     * arguments.)<p>
     *
     * When this routine is overridden, the new method body should
     * always end with <code>return super.processOption(option, args,
     * offset)</code>.<p>
     */
    //@ requires option!=null && \nonnullelements(args)
    //@ requires 0<=offset && offset<=args.length
    //@ ensures 0<=\result && \result<=args.length
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
	    if (offset>=args.length) {
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
     * Print our usage message to <code>System.err</code>. <p>
     */
    public void usage(String name) {
	System.err.print(name + ": usage: " + name + " options* ");
	System.err.print(showNonOptions());
	System.err.println(" where options include:");
	System.err.print(showOptions(false));
    }
    
    /**
     * Print non-option usage info to the given String.
     */
    public String showNonOptions() { return ""; }
    
    /**
     * Print option information to the given StringBuffer.  Each
     * line should be preceeded by two blank spaces
     * and followed by a line separator. <p>
     *
     * If the argument is true, then all options are printed, including
     * experimental options; otherwise, just the options expected to be
     * used by standard users are printed.
     *
     * Each overriding method should first call
     * <code>super.showOptions()</code>.<p>
     */
    public String showOptions(boolean all) {
    	StringBuffer sb = new StringBuffer();
	sb.append("  -v"); sb.append(eol);	
	sb.append("  -quiet"); sb.append(eol);
	sb.append("  -bootclasspath <classpath>"); sb.append(eol);	
	sb.append("  -classpath <classpath>"); sb.append(eol);
	sb.append("  -noCautions"); sb.append(eol);
	return sb.toString();
    }
    
    final public String eol = System.getProperty("line.separator");
}

