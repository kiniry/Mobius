/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe;


/**
 * <code>Tool</code> is an abstract class for tools. <p>
 *
 * Tools are command-line applications invoked by calling their static
 * <code>main(String[])</code> method.<p>
 */

public abstract class Tool {

    /**************************************************
     *    Exit codes                                  *
     **************************************************/

    static public final int okExitCode = 0;
    static public final int badUsageExitCode = 1;
    static public final int errorExitCode = 2;
    static public final int outOfMemoryExitCode = 3;

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
    public void usage() {
    	options.usage(name());
    }

    public void badOptionUsage(Exception e) {
        System.err.println(name() + ": " + e.getMessage());
        if (!options.quiet) usage();
    }

    /***************************************************
     *                                                 *
     * Generic option processing:		       *
     *                                                 *
     **************************************************/

    /** 
     * A statically held Options object.  The object is static to
     * facilitate using the options in other classes throughout the
     * program.  All processing and reporting of options is managed by
     * this object.
     */
     
    static public Options options = null;
    
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
		// int result = t.run(args);
		// if (result != 0) System.exit(result);
    }


    /**
     * A tool's main entry point; <code>args</code> are the
     * command-line arguments we have been invoked with. <p> 
     * @return the exit code (0 = success, >0 is a failure)
     */
    //@ requires \nonnullelements(args)
    public abstract int run(String[] args);

    /**
     * Compute the time used from a start time to now, then return it
     * in a user readable form.
     */
    /*@ ensures \result != null */
    public static String timeUsed(long startTime) {
        //if (options.testMode) return "TIME";
        long delta = java.lang.System.currentTimeMillis() - startTime;
     
        return (delta/1000.0) + " s";
    }
 
    public static long currentTime() {
        return java.lang.System.currentTimeMillis();
    }
 
}
