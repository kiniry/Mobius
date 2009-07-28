/* Copyright 2000, 2001, Compaq Computer Corporation */

package houdini;

import houdini.util.*;
import java.net.*;
import java.util.*; 
import java.io.*;


/**
 * This class handles options common to both HoudiniServer and HoudiniClient.
 * It is based on javafe.FrontEndTool.
 */
public abstract class OptionHandler extends javafe.Tool {
    
    public abstract String name(); 
    
    /**
     ** Print our usage message to <code>System.err</code>. <p>
     **/
    public final void usage() {
	System.err.print(name() + ": usage: " + name() + " options* ");
	System.err.println("where options include:");
	showOptions();
    }
    
    public void showOptions() {
	System.err.println(" -debug \n" +
	                   " -nodebug \n" +
	                   " -log <key>\n" + 
	                   " -port <port>\n" +
	                   " -host <name> \n" +
	                   " -ubp <universal back pred file> \n" +
	                   " -logToFile \n"
	                   );
    }
   
    /** port for communication */
    public int port = 17777;
    
    /** host of server */
    public String host = null;

    /** directory where vc files live */
    String vcdir = "./";

    /** unversial background predicate to use */
    String univBackPredFile = "./UnivBackPred.ax";

    /** log output to file */
    public boolean logToFile = false;

    /** output stream for logging (default is System.out) */
    PrintStream logFile = System.out;

    /**
     ** Process next tool option. <p>
     **
     ** See <code>Tool.processOption</code> for the complete
     ** specification of this routine.<p>
     **
     ** This routine handles the standard front-end options, storing the
     ** resulting information in the preceding instance variables and
     ** <code>Info.on</code>.<p>
     **/
    public int processOption(String option, String[] args, int offset) {
	if (option.equals("-debug")) {
	    Debug.debug = true;
	    return offset;
	} else if (option.equals("-nodebug")) {
	    Debug.debug = false;
	    return offset;
	} else if (option.equals("-logToFile")) {
	    this.logToFile = true;
	    return offset;
	} else if (option.equals("-port")) {
	    if (offset>=args.length) {
	        usage();
	        System.exit(usageError);
	    }
	    port = Integer.parseInt(args[offset]);
	    return offset+1;
	} else if (option.equals("-ubp")) {
	    if (offset>=args.length) {
	        usage();
	        System.exit(usageError);
	    }
	    univBackPredFile =args[offset];
	    return offset+1;
	} else if (option.equals("-host")) {
	    if (offset>=args.length) {
	        usage();
	        System.exit(usageError);
	    }
            host = args[offset];
	    return offset+1;
	} else if (option.equals("-vcdir")) {
	    if (offset>=args.length) {
	        usage();
	        System.exit(usageError);
	    }
	    vcdir=args[offset];
	    if (!vcdir.endsWith("/") && !vcdir.endsWith("\\")) {
	        vcdir += "/";
	    }
	    return offset+1;
	} else if (option.equals("-log")) {
	    if (offset>=args.length) {
	        usage();
	        System.exit(usageError);
	    }
	    Log.logToStdout(args[offset], Log.LL_HIGH);
	    return offset+1;
	} 
        return super.processOption(option, args, offset);
    }
    
    /**
     ** A tool's main entry point; <code>args</code> are the
     ** command-line arguments we have been invoked with. <p> 
     **/
    public void run(String[] args) {
	int offset = processOptions(args);
    }


    /**
     * Print log message with date at front 
     */
    public void logWithDate(String s) {
        logFile.println("["+ Utility.getDateString() + "] " + s);
    }

    public static String shortName(String s) {
	int lastSlash = s.lastIndexOf("/");
	if (lastSlash == -1) return s;
	return s.substring(lastSlash + 1);
    }

    
}

