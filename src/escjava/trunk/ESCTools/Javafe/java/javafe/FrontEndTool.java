/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe;


import javafe.ast.PrettyPrint;
import javafe.ast.StandardPrettyPrint;

import javafe.reader.StandardTypeReader;
import javafe.parser.PragmaParser;

import javafe.tc.OutsideEnv;
import javafe.tc.TypeCheck;

import javafe.util.*;


/**
 * <code>FrontEndTool</code> is an abstract class for tools that use
 * our Java front end. <p>
 *
 * It handles parsing the standard options for setting
 * up the front end and initializing the front end using those options.
 * At the end of a run, it prints a count of how many cautions,
 * warnings, and errors occurred (cf. <code>ErrorSet</code>).  It also
 * handles catching <code>FatalError</code>s (see
 * <code>ErrorSet.fatal</code>).  The remaining processing, if any, is
 * front-end-tool specific.<p>
 */

public abstract class FrontEndTool extends Tool {
    

    /***************************************************
     *                                                 *
     * Standard front-end setup:		       *
     *                                                 *
     **************************************************/

    /**
     * Setup: initialize the front end using the standard
     * front-end-tool option variables (<code>userPath, sysPath</code>). <p>
     *
     * This can be done only once.  The standard front-end-tool option
     * variables have no effect after this point.  May exit with an
     * error (via <code>ErrorSet.fatal</code>).<p>
     *
     * Ensures <code>OutsideEnv</code> has been properly initialized
     * (except if an error occurs).<p>
     *
     * Also initializes PrettyPrint.inst and TypeCheck.inst to their
     * default front end values.
     */
    public void setup() {

		String classPath = options.userPath;
		if (classPath==null)
		    // The behavior of this code differs between 1.1 and 1.2:
		    classPath = javafe.filespace.ClassPath.current();
	
		String sys = options.sysPath;
		if (sys==null)
		    // This works only on Sun implementations of Java...
		    sys = System.getProperty("sun.boot.class.path", null);
	
		if (sys!=null && !sys.equals("")) {
		    if (!classPath.equals("")) {
			classPath += System.getProperty("path.separator", ":");
		    }
		    classPath += sys;
		}
	
		Info.out("[Full classpath is " + classPath + "]");
	
		OutsideEnv.init(makeStandardTypeReader(classPath,
						       makePragmaParser()));
	
		PrettyPrint.inst = makePrettyPrint();
		TypeCheck.inst = makeTypeCheck();
    }

    /** Called to clear any static initializations, so that the parser can be
        called multiple times within one process.  Called as part of
        construction of a new Main.
    */
    public void clear() {
        ErrorSet.clear();
        OutsideEnv.clear();
    }

    /**
     * Called to obtain the StandardTypeReader to be used for locating
     * and reading in types.
     */
    //@ ensures \result!=null
    public StandardTypeReader makeStandardTypeReader(String path,
						     PragmaParser P) {
        return StandardTypeReader.make(path, P);
    }

    /**
     * Called to obtain the pragma parser to be used for parsing
     * input files.  If <code>null</code> is returned, then no pragma
     * parsing is done.  (By default, returns <code>null</code>).
     */
    public PragmaParser makePragmaParser() {
        return null;
    }
    
    /**
     * Called to create a new Options object.
     */
     //@ ensures \result != null;
    public Options makeOptions() {
     	return new Options();
    }
    
    public int processOptions(String[] args) throws UsageError {
        return options.processOptions(args);
    }

    /**
     * Called to obtain the pretty printer to set
     * <code>PrettyPrint.inst</code> to.  May not return
     * <code>null</code>.  By default, returns
     * <code>javafe.ast.StandardPrettyPrint</code>.
     */
    //@ ensures \result!=null
    public PrettyPrint makePrettyPrint() {
        return new StandardPrettyPrint();
    }

    /**
     * Called to obtain an instance of the javafe.tc.TypeCheck class
     * (or a subclass thereof). May not return <code>null</code>.  By
     * default, returns <code>javafe.tc.TypeCheck</code>.
     */
    //@ ensures \result!=null
    public TypeCheck makeTypeCheck() {
        return new TypeCheck();
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
        // Tool t = new FrontEndTool();
        // int result = t.run(args);
        // if (result != 0) System.exit(result);
    }


    /**
     * A tool's main entry point; <code>args</code> are the
     * command-line arguments we have been invoked with. <p> 
     */
    public final int run(String[] args) {
	try {
	    // Handle all tool options:
	    options = makeOptions();
	    int offset = processOptions(args);
	    if (options.issueUsage) {
		usage();
		return okExitCode;
	    }
	
	    // Setup the front end using them:
	    setup();
		
	    // Do our front-end-tool-specific processing:
	    frontEndToolProcessing(args, offset);
	
        } catch (UsageError e) {
            badOptionUsage(e);
	    ErrorSet.errors++; // Just so that the JUnit tests detect that
				// an error message was issued
            return badUsageExitCode;
        } catch (FatalError e) {
	    Info.out("[" + name() + " exiting due to a fatal error]");
	}
	
	if (ErrorSet.cautions!=0)
	    System.out.println(ErrorSet.cautions + " caution"
		+ (ErrorSet.cautions>1 ? "s" : ""));
	if (ErrorSet.warnings!=0)
	    System.out.println(ErrorSet.warnings + " warning"
		+ (ErrorSet.warnings>1 ? "s" : ""));
	if (ErrorSet.errors!=0)
	    System.out.println(ErrorSet.errors + " error"
		+ (ErrorSet.errors>1 ? "s" : ""));
	
	// If we call exit here, we will break GUI-based clients.
	// Return error status to caller:
	if (ErrorSet.errors>0)
	    return errorExitCode;
	else {
	    return okExitCode;
	}
    }

    /**
     * Perform any front-end-tool-specific processing. <p>
     *
     * The remaining arguments are <code>args[offset]</code>,
     * <code>args[offset+1]</code>, ...<p>
     */
    //@ requires \nonnullelements(args)
    //@ requires 0<=offset && offset<=args.length
    public abstract void frontEndToolProcessing(String[] args, int offset);
}
