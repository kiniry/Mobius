/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe;


import javafe.ast.PrettyPrint;
import javafe.ast.StandardPrettyPrint;

import javafe.reader.StandardTypeReader;
import javafe.parser.PragmaParser;

import javafe.tc.OutsideEnv;
import javafe.tc.TypeCheck;

import javafe.util.*;

import java.util.ArrayList;

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
    protected String compositeSourcePath;
    protected String compositeClassPath;
    public void setupPaths() {

	String classPath = options.userPath;
	if (classPath==null)
	    // The behavior of this code differs between 1.1 and 1.2:
	    classPath = javafe.filespace.ClassPath.current();

	String sourcePath = options.userSourcePath;

	String sys = options.sysPath;
	if (sys==null)
	    // This works only on Sun implementations of Java...
	    sys = System.getProperty("sun.boot.class.path", null);

	if (sys != null && !sys.equals("")) {
	    if (!classPath.equals("")) {
		classPath += System.getProperty("path.separator", ":");
	    }
	    classPath += sys;
	}
	compositeSourcePath = sourcePath;
	compositeClassPath = classPath;
    }

    public void setup() {
	setupPaths();
	Info.out("[Full classpath is " + compositeClassPath + "]");
	Info.out("[Full sourcepath is " + compositeSourcePath + "]");

	// It is ok if sourcePath is null; it then shares a database of the
	// contents of the directory path with classpath, rather than 
	// creating a separate, identical database.
	OutsideEnv.init(makeStandardTypeReader(compositeClassPath, 
					       compositeSourcePath,
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
	// FIXME LocationManagerCorrelatedReader.clear();
        OutsideEnv.clear();
    }

    /**
     * Called to obtain the StandardTypeReader to be used for locating
     * and reading in types.
     */
    //@ ensures \result != null;
    public StandardTypeReader makeStandardTypeReader(String path,
						     String sourcePath,
						     PragmaParser P) {
        return StandardTypeReader.make(path, sourcePath, P);
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
    
    public void processOptions(String[] args) throws UsageError {
        options.processOptions(args);
    }

    /**
     * Called to obtain the pretty printer to set
     * <code>PrettyPrint.inst</code> to.  May not return
     * <code>null</code>.  By default, returns
     * <code>javafe.ast.StandardPrettyPrint</code>.
     */
    //@ ensures \result != null;
    public PrettyPrint makePrettyPrint() {
        return new StandardPrettyPrint();
    }

    /**
     * Called to obtain an instance of the javafe.tc.TypeCheck class
     * (or a subclass thereof). May not return <code>null</code>.  By
     * default, returns <code>javafe.tc.TypeCheck</code>.
     */
    //@ ensures \result != null;
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

    /** Parses the options into a new instance of an Options
	subclass.  Returns -1 if all is well and the program
	should continue with processing.  Otherwise returns
	an exit code.
<P>
	If the argument is null, the tool is initialized with the
	existing options.
     */
    public int handleOptions(String[] args) {
	if (args != null) {
	try {
	    // Handle all tool options:
	    options = makeOptions();
	    processOptions(args);
	    if (options.issueUsage) {
		usage();
		return okExitCode;
	    }
        } catch (UsageError e) {
            badOptionUsage(e);
	    ErrorSet.errors++; // Just so that the JUnit tests detect that
				// an error message was issued
            return badUsageExitCode;
        } catch (FatalError e) {
	    Info.out("[" + name() + " exiting due to a fatal error]");
	}
	}
	// Setup the front end using the options:
	setup();
	return -1;
    }

    /**
     * A tool's main entry point; <code>args</code> are the
     * command-line arguments we have been invoked with. <p> 
     */
    //@ requires args != null;
    public final int run(String[] args) {
	int r = handleOptions(args);
	if (r != -1) return r;
	
	if (ErrorSet.errors == 0) try {
		
	    // Do our front-end-tool-specific processing:
	    frontEndToolProcessing(options.inputEntries);
	
        } catch (FatalError e) {
	    Info.out("[" + name() + " exiting due to a fatal error]");
	}
	
	if (ErrorSet.cautions != 0)
	    System.out.println(ErrorSet.cautions + " caution"
		+ (ErrorSet.cautions>1 ? "s" : ""));
	if (ErrorSet.warnings != 0)
	    System.out.println(ErrorSet.warnings + " warning"
		+ (ErrorSet.warnings>1 ? "s" : ""));
	if (ErrorSet.errors != 0)
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
    public abstract void frontEndToolProcessing(ArrayList args);
}
