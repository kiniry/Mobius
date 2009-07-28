/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.util;

import java.io.*;
import javafe.FrontEndTool;

/**
 * The <code>ErrorSet</code> class is responsible for displaying
 * cautions, warnings, ordinary errors, and fatal errors to the user.
 * It maintains counts of how many cautions, warnings, and errors have
 * been reported so far.
 *
 * <p> Currently, reporting is done via printing all messages to
 * <code>System.out</code>.  Messages are accompanied by an indication
 * of whether they are a caution, a warning, an ordinary error, or a
 * fatal error.
 *
 * <p> Messages are printed as soon as they are reported.  A future
 * version of <code>ErrorSet</code> may group together messages
 * concerning the same file to be printed in location sorted order
 * once the file has been processed fully.  (This will require adding
 * some kind of <code>end_of_file(F)</code> call.)
 *
 * <p> Rough rules for determining what class to report something as:
 * <dl>
 * <dt> Error: <dd> something that is definitely wrong and which
 *	prevents processing everything the tool was requested to work
 *	on.
 *
 * <dt> Fatal Error: <dd> similar except that it prevents any further
 *      processing at all.  (Tools may continue after ordinary errors
 *      by aborting processing of some, but not all, parts of the
 *      input program.)
 *
 * <dt> Caution: <dd>
 *      (1) something that is technically illegal according to the
 *	language spec(s), but the tool accepts anyways for
 *	compatibility with other tools.  (It must not force
 *      aborting.) <br>
 *      (2) something that inhibits the tool's ability to catch
 *	errors, but is not wrong.  Often caused by poor use of
 *	annotations in escjava.
 *
 * <dt> Warning: <dd>something that the Tool believes, but is not
 *	sure, is a serious problem.
 * </dl>
 *
 * @see Location
 * @see FatalError
 */

public class ErrorSet
{
    // Prevent javadoc from displaying a public constructor
    private ErrorSet() {};


    /***************************************************
     *                                                 *
     * Class Variables:				       *
     *                                                 *
     **************************************************/

    /**
     * The number of cautions reported so far.
     */
    public static int cautions = 0;


    /**
     * The number of warnings reported so far.
     */
    public static int warnings = 0;


    /**
     * The number of errors reported so far, including fatal errors.
     */
    public static int errors = 0;

    /**
     * The number of fatal errors so far (some my have been caught and handled)
     */
    public static int fatals = 0;

    /**
     * If <code>gag</code> is true, then no output is produced by
     * <code>ErrorSet</code> methods (useful for test harnesses).
     *
     * Defaults to false.<p>
     */
    public static boolean gag = false;

    /** Resets all error and warning counts. */
    public static void clear() {
	fatals = 0;
	errors = 0;
	warnings = 0;
	cautions = 0;
	gag = false;
    }

    /***************************************************
     *                                                 *
     * Reporting entry points:			       *
     *                                                 *
     **************************************************/

    /**
     * Report a caution. <p>
     * 
     * The message will be marked as a caution when it is displayed to
     * the user.  Increments <code>cautions</code> by one.<p>
     */
    public static void caution(String msg) {
	if (FrontEndTool.options.noCautions) {

	    return;
	}
	cautions++;
	report(CAUTION, msg);
    }

    /**
     * Report a caution associated with a location. <p>
     * 
     * Precondition: <code>loc</code> must be a regular location or a
     * whole file location.<p>
     *
     * The message will be marked as a caution when it is displayed to
     * the user.  Increments <code>cautions</code> by one.<p>
     */
    //@ requires loc != Location.NULL
    public static void caution(int loc, String msg) {
	if (FrontEndTool.options.noCautions) {
	    return;
	}
	cautions++;
	report(loc, CAUTION, msg);
    }

    public static void caution(int loc, String msg, int addLoc) {
	if (FrontEndTool.options.noCautions) {
	    return;
	}
	cautions++;
	report(loc, CAUTION, msg);
	if (addLoc != Location.NULL)
		report(addLoc, "Associated declaration", "");
    }


    /**
     * Report a warning. <p>
     * 
     * The message will be marked as a warning when it is displayed to
     * the user.  Increments <code>warnings</code> by one.<p>
     */
    public static void warning(String msg) {
	warnings++;
	report(WARNING, msg);
    }

    /**
     * Report a warning associated with a location. <p>
     * 
     * Precondition: <code>loc</code> must be a regular location or a
     * whole file location.<p>
     *
     * The message will be marked as a warning when it is displayed to
     * the user.  Increments <code>warnings</code> by one.<p>
     */
    //@ requires loc != Location.NULL
    public static void warning(int loc, String msg) {
	warnings++;
	report(loc, WARNING, msg);
    }


    /**
     * Report an ordinary error. <p>
     * 
     * The message will be marked as an error when it is displayed to
     * the user.  Increments <code>errors</code> by one.<p>
     */
    public static void error(String msg) {
	errors++;
	report(ERROR, msg);
    }

    /**
     * Report an ordinary error associated with a location. <p>
     * 
     * Precondition: <code>loc</code> must be a regular location or a
     * whole file location.<p>
     *
     * The message will be marked as an error when it is displayed to
     * the user.  Increments <code>errors</code> by one. <p>
     */
    //@ requires loc != Location.NULL
    public static void error(int loc, String msg) {
	errors++;
	report(loc, ERROR, msg);
    }

    public static void error(int loc, String msg, int addLoc) {
	errors++;
	report(loc, ERROR, msg);
	if (addLoc != Location.NULL)
	    report(addLoc, "Associated declaration", "");
    }


    /**
     * Report a fatal error.  Warning: This method does not
     * return normally!<p>
     * 
     * The variable <code>errors</code> is incremented by one, the
     * error reported as a fatal error, and then an unchecked
     * <code>FatalError</code> exception is thrown.  The top level of a
     * <code>Tool</code> is responsible for catching the
     * <code>FatalError</code>, so that it can do whatever cleanup is
     * required before exiting.<p>
     */
    //@ ensures false
    public static void fatal(String msg) /*throws FatalError*/ {
	if (msg != null) {
	    fatals++;
	    errors++;
	    report(FATALERROR, msg);
	}
	throw new FatalError();
    }    //@ nowarn Exception

    /**
     * Report a fatal error associated with a location.  Warning: This
     * method does not return normally!<p>
     * 
     * Precondition: <code>loc</code> must be a regular location or a
     * whole file location.<p>
     *
     * The variable <code>errors</code> is incremented by one, the
     * error reported as a fatal error, and then an unchecked
     * <code>FatalError</code> exception is thrown.  The top level of a
     * <code>Tool</code> is responsible for catching the
     * <code>FatalError</code>, so that it can do whatever cleanup is
     * required before exiting.<p>
     */
    //@ requires loc != Location.NULL
    //@ ensures false
    public static void fatal(int loc, String msg) /*throws FatalError*/ {
	fatals++;
	errors++;
	report(loc, FATALERROR, msg);
	throw new FatalError();
    }    //@ nowarn Exception

    /** Special call to report unimplemented features, so they can be caught
	and handled more easily.
    */
    public static void notImplemented(boolean print, int loc, String msg) {
	if (print) report(loc, "Not implemented", msg);
	throw new NotImplementedException(msg);
    }

    /***************************************************
     *                                                 *
     * Common code for reporting:		       *
     *                                                 *
     **************************************************/

    // Constants for use as the type field of report:

    private static final String CAUTION		= "Caution";
    private static final String WARNING		= "Warning";
    private static final String ERROR		= "Error";
    private static final String FATALERROR	= "Fatal error";


    /**
     * Report general information. <p>
     *
     * Type contains a non-null String describing the type of the
     * information (usually one of the above constants).  The
     * information itself is contained in the non-null String
     * msg.<p>
     *
     * This function is not responsible for incrementing counts or
     * other ErrorSet functionality.<p>
     */
    private static void report(/*@ non_null */ String type, /*@ non_null */ String msg) {
	if (! gag)
	    report(type + ": " + msg);

        // Hack so we can see where error occurred, for debugging:
	if (javafe.Tool.options.showErrorLocation) dump(null);
	
    }

    /**
     *  Reports a general message, implemented here in order to
     *  have a single location through which error reporting happens.
     */
    public static void report(/*@ non_null @*/ String msg) {
	System.out.println(msg);
    }


    /**
     * Report information associated with a location. <p>
     *
     * Type contains a non-null String describing the type of the
     * information (usually one of the above constants).  The
     * information itself is contained in the non-null String
     * msg.<p>
     *
     * Precondition: <code>loc</code> must be a regular location or a
     * whole file location.<p>
     *
     * This function is not responsible for incrementing counts or
     * other ErrorSet functionality.<p>
     */
    //@ requires loc != Location.NULL
    private static void report(int loc, String type, String msg) {
	if (gag)
	    return;

        // Hack so we can see where error occurred, for debugging:
	if (javafe.Tool.options.showErrorLocation) dump(null);

	if (loc==Location.NULL)
	    Assert.fail("NULL location erroneously passed to ErrorSet;"
			+ " Associated information is `" + type
			+ ": " + msg + "'");

	// Display the file human-readable name and line # if available:
	System.out.print(Location.toFileName(loc) + ":");
	if (!Location.isWholeFileLoc(loc))
	    System.out.print(Location.toLineNumber(loc) + ":");

	// Display the type of the information & the information:
	System.out.println(" " + type + ": "+ msg);

	// Display which column # visually if available:
	if (!Location.isWholeFileLoc(loc))
	    displayColumn(loc);
    }


    /***************************************************
     *                                                 *
     * Utility routines:			       *
     *                                                 *
     **************************************************/

    /**
     * Return a new InputStream for the file that loc refers to or null
     * if an I/O error occurs while attempting to open the stream. <p>
     *
     * Precondition: <code>loc</code> must be a regular location or a
     * whole file location.<p>
     *
     * No error is reported if an I/O error occurs.
     */
    //@ requires loc != Location.NULL
    private static InputStream getFile(int loc) {
	try {
	    return Location.toFile(loc).getInputStream();
	} catch (IOException e) {
	    return null;
	}
    }


    /**
     * Return the line loc refers to or null if an I/O error occurs
     * while attempting to read the line in. <p>
     *
     * Precondition: <code>loc</code> is a regular location (e.g., not
     * a whole-file location).<p>
     *
     * No error is reported if an I/O error occurs.
     */
    //@ requires loc != Location.NULL
    private static String getLine(int loc) {
	InputStream i = getFile(loc);
	if (i==null)
	    return null;

        try {
	    /*
	     * skip to the start of the line in question:
	     */
	    long charsLeft = (Location.toOffset(loc)-1)
			    - Location.toColumn(loc);
	    while ((charsLeft -= i.skip(charsLeft))>0) {
		i.read();
		charsLeft--;
	    }

	    StringBuffer line = new StringBuffer(100);
	    for (int c=i.read(); c != 10/*newline*/ && c!= -1/*EOF*/; c=i.read())
		line.append((char)c);

	    i.close();
	    return line.toString();
	} catch (IOException e) {
	    return null;
	}
    }


    /** See documentation for two-argument version of <code>displayColumn</code>.
      * This version differs in that the default clip policy is applied.
      */
    //@ requires loc != Location.NULL
    public static void displayColumn(int loc) {
      displayColumn(loc, null);
    }

    /**
     * Display (part of) the line that loc occurs on, then indicate via
     * a caret (^) which column loc points to. <p>
     *
     * Tabs are expanded before the line is displayed using 8-character
     * tab stops.<p>
     *
     * Precondition: <code>loc</code> is a regular location (e.g., not
     * a whole-file location).<p>
     *
     * If an I/O error does occur, then the user is informed of the
     * column number and that the line in question is not available; no
     * error is reported.
     *
     * By using a non-null <code>policy</code> argument, a caller can fine-
     * tune the policy used for introducing ellipses in the printed line.
     */
    //@ requires loc != Location.NULL
    public static void displayColumn(int loc, ClipPolicy policy) {
	String line = getLine(loc);
	int col = Location.toColumn(loc);	// zero-based
	if (line==null) {
	     System.out.println("(line text not available; see column "
					+ col + ")");
	     return;
	}


	/*
	 * Expand tabs in line, keeping col in sync:
	 */
	StringBuffer adjusted = new StringBuffer(100);
	int x = 0;		// tab-adjusted location on line (0-based)
	int acol = col;
	for (int i=0; i<line.length(); i++) {
	    char c = line.charAt(i);
	    if (c != '\t') {
		adjusted.append(c);
		x++;
	    } else {
		adjusted.append(' ');		// Tab always non-zero skip
		x++;
		while (x%8 != 0) {		// Skip to next tab stop
		    adjusted.append(' ');
		    x++;

		    if (i<col)
			acol++;
		}
	    }
	}
	line = adjusted.toString();
	col = acol;


	// Handle case where file has been modified since it was last read:
	if (col>=line.length()) {
	     System.out.println("(line text no longer available; see column "
					+ col + ")");
	     return;
	}


	String noclipLine = line;
	int noclipCol = col;
	int LINELENGTH = 80;	// HACK? !!!!

	/*
	 * Clip the start of line if column would otherwise be too far to
	 * the right:
	 */
	if (col>LINELENGTH-15) {
	    int clip = col-(LINELENGTH/2) + 5;
	    col = (LINELENGTH/2);
	    line = " ... " + line.substring(clip);
	}

	/*
	 * Clip the end of line if it would go past the edge of the screen:
	 */
	if (line.length()>LINELENGTH-10) {
	    line = line.substring(0, LINELENGTH-10) + " ...";
	} else if (policy != null &&
		   !policy.containsEndOfConstruct(noclipLine, noclipCol)) {
	    line += " ...";
	}

	System.out.println(line);

	// Display a ^ where the col. # is:
	for (int o=0; o<col; o++)
	  System.out.print(" ");
	System.out.println("^");
    }

    /** Prints to System.out the given String (if not null)
        and a current stack trace,
	to be used for debugging with print statements.
    */
    //@ modifies \nothing; // except the content of System.out
    static public void dump(String s) {
	if (s != null) System.out.println(s);
	(new Exception()).printStackTrace();
    }
}
