package javafe;

import javafe.util.UsageError;

/**
 * This class holds the command-line options specific to the SrcTool class.
 */
 
public class SrcToolOptions extends Options
{
    //**************************************************************************
    //  Hard-coded behavior
    //**************************************************************************
    
    /**
     * Do we allow the <code>-avoidSpec</code> option?  Defaults to
     * yes.
     */
    public static boolean allowAvoidSpec = true;

    /**
     * Do we allow the -depend option?  Defaults to yes.
     */
    public static boolean allowDepend = true;

    //****************************************************************************
    // Options
    //****************************************************************************
    
    /**
     * Should we avoid specs for all types loaded after the initial
     * set of source files?
     *
     * <p> Defaults to false.  Set by -avoidSpec option.
     *
     * <p> Note: if <code>processRecursively</code> is set, then we
     * always avoid specs.
     */
    public boolean avoidSpec = false;

    /**
     * Should we process files recursively?  Defaults to no, 
     * can be set by a sub-class, or the -depend option.
     *
     * <p> Warning: this needs to be set before option processing is
     * finished!
     */
    public boolean processRecursively = false;

    /**
     * The list of filenames on the command line; this Vector is aliased
     * with a variable in SrcTool.
     */
    
    //************************************************************************
    // Support routines
    //************************************************************************

    // @overrides Options.processOption(String, String[], int)

    public int processOption(String option, String[] args, int offset) 
        throws UsageError {
 	if (option.equals("-depend") && allowDepend) {
	    processRecursively = true;
	    return offset;
	} else if (option.equals("-avoidSpec") && allowAvoidSpec) {
	    avoidSpec = true;
	    return offset;
	} else
	    // Pass on unrecognized options:
	    return super.processOption(option, args, offset);
    }
        
    /**
     * Print non-option usage info to <code>System.err</code>.  Output
     * must include at least one newline.
     */
    public String showNonOptions() {
		return ("<source files>");
    }

    /**
     * Print option information to <code>System.err</code>.  Each
     * printed line should be preceeded by two blank spaces.
     *
     * <p> Each overriding method should first call
     * <code>super.showOptions()</code>.
     */
    public String showOptions(boolean all) {
	String[][] data1 = {{"-avoidSpec",""}};
	String[][] data2 = {{"-depend",""}};

        StringBuffer sb = new StringBuffer(super.showOptions(all));
	
	if (allowAvoidSpec) sb.append(showOptionArray(data1));
	
	if (allowDepend) sb.append(showOptionArray(data2));
		
	return sb.toString();
    }

}
