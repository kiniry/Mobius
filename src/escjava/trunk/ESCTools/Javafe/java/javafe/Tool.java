/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe;


/**
 * <code>Tool</code> is an abstract class for tools. <p>
 *
 * Tools are command-line applications invoked by calling their static
 * <code>main(String[])</code> method.<p>
 */

public abstract class Tool {

    /***************************************************
     *                                                 *
     * Generating a usage message:		       *
     *                                                 *
     **************************************************/

    /**
     * Return the non-null name of this tool.  E.g., "ls" or "cp".<p>
     *
     * Used in usage and error messages.<p>
     */
    //@ ensures \result!=null
    public abstract String name();


    /**
     * Print our usage message to <code>System.err</code>. <p>
     */
    public abstract void usage();


    /***************************************************
     *                                                 *
     * Generic option processing:		       *
     *                                                 *
     **************************************************/

    //* Exit status to use for a usage error:
    public static final int usageError = 1;


    /**
     * Process tool options contained in <code>args</code>. <p>
     *
     * If an error occurs, <code>usage()</code> is called then we exit
     * the program with error status <code>usageError</code>.
     * Otherwise, the offset to the first non-option in
     * <code>args</code> is returned.  E.g., this routine
     * "consumes" <code>args[0]</code>, ...,
     * <code>args[</code><i>returned_value</i><code>-1]</code>.<p>
     */
    //@ requires \nonnullelements(args)
    //@ ensures 0<=\result && \result<=args.length
    public final int processOptions(String[] args) {
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
     * This routine handles processing the next option from the
     * command-line arguments.  It is passed the option in question
     * (<code>option</code>), which will always start with a '-'
     * character, and the remaining command-line arguments (not
     * counting <code>option</code>)
     * (<code>args[offset]</code>,...,<code>args[args.length-1]</code>).<p>
     *
     * If the option is erroneous, an error should be reported to
     * <code>System.err</code>; <code>System.exit</code> should then be
     * called with <code>usageError</code>.  Otherwise, the offset to
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
    public int processOption(String option, String[] args, int offset) {
	System.err.println(name() + ": unknown option: " + option);
	System.err.println();
	usage();
	System.exit(usageError);

	return offset;			// make compiler happy
    }


    /***************************************************
     *                                                 *
     * Main processing code:			       *
     *                                                 *
     **************************************************/

    /**
     * Start up an instance of this tool using command-line arguments
     * <code>args</code>. <p> 
     *
     * <b>Note</b>: this code needs to be copied verbatim to each
     * subclass of <code>Tool</code> except with the name of the actual
     * subclass inserted after the new operator and the comment
     * characters (//) removed.<p>
     *
     * (This needs to be done because static methods cannot be
     * inherited.)<p>
     */
    //@ requires \nonnullelements(args)
    public static void main(String[] args) {
	// Tool t = new Tool();
	// t.run(args);
    }


    /**
     * A tool's main entry point; <code>args</code> are the
     * command-line arguments we have been invoked with. <p> 
     */
    //@ requires \nonnullelements(args)
    public abstract void run(String[] args);
}
