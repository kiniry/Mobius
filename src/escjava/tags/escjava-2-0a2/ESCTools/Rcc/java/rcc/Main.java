/* Copyright 2000, 2001, Compaq Computer Corporation */

// SNF Mon Jun 28 17:28:37 1999
// based on main from esc
package rcc;


import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;
import java.io.*;

import javafe.ast.*;

import rcc.ast.*;
import rcc.ast.RccPrettyPrint;
import rcc.ast.TagConstants;

import javafe.reader.StandardTypeReader;
//import rcc.reader.EscTypeReader;

import javafe.parser.PragmaParser;


import javafe.tc.*;
import rcc.tc.TypeCheck;

import javafe.util.*;


/**
 ** Top level control module for ESC for Java. <p>
 **
 ** This class (and its superclasses) handles parsing
 ** <code>rcc</code>'s command-line arguments and orchestrating the
 ** other pieces of the front end and rcc to perform the requested
 ** operations.<p>
 **
 ** @see javafe.Tool
 ** @see javafe.SrcTool
 **/

public class Main extends javafe.SrcTool {
    
    /** Our version number **/
    public final String version = "0.233.  Based on escjava 1.1.5a, 16 June 1999";
    public Vector commandLineFiles;
    
    public static Main inst = null;
    
    public Main() {
	inst = this;
    }
    
    /***************************************************
     *                                                 *
     * Global rcc flags:			       *
     *                                                 *
     ***************************************************/
    
    /*
     * These are set by the command-line switches of the same name.
     * They default to false (unset).
     */
    
    public static boolean quiet	= false;
    
    public static boolean wall	= false; // wall
    public static boolean noho	= false; // ignore no holds
    public static boolean agt	= false; // add guarded_by this
    public static boolean prg	= false; // print redundant guards
    public static boolean pjt	= false; // print java w/ types
    public static boolean pun	= false; // print untriggered no_warns
    public static boolean tse   = false; // print stack trace on warning
    public static boolean chl   = false; // constructor holds locks
    public static boolean dts   = false; // default is thread_shared
    public static boolean ihl  = false; //  initializer holds lock
    public static boolean ihnl  = false; //  initializer holds lock
    public static Set ignoreAnnSet = null;
    
    public static boolean stats = false;
    public static boolean plainWarning = false;
    public static boolean suggest = false; // suggest fixes (for wizard)
    public static int startLine;
    
    /***************************************************
     *                                                 *
     * Generating an options message:		       *
     *                                                 *
     ***************************************************/
    
    /**
     ** Return the name of this tool.  E.g., "ls" or "cp".<p>
     **
     ** Used in usage and error messages.<p>
     **/
    public String name() { return "rcc"; }
    
    /**
     ** Print option option information to
     ** <code>System.err</code>. <p>
     **/
    public void showOptions() {
	super.showOptions();
	System.err.println(" -pjt\t\t\t\t print code with types");
	System.err.println(" -agt\t\t\t\t assume unguarded shared fields guarded by this");
	System.err.println(" -prg\t\t\t\t print redundant guards");
	System.err.println(" -noho\t\t\t\t ignore no_hold's");
	System.err.println(" -wall\t\t\t\t print all warnings");
	System.err.println(" -pun\t\t\t\t print untriggered no_warn's / unneeded holds");
	System.err.println(" -chl\t\t\t\t assume constructor holds self lock");
	System.err.println(" -dts\t\t\t\t classes on command line are thread_shared by default");
	System.err.println(" -ihl\t\t\t\t initializer blocks hold self/class lock");
	System.err.println(" -ihnl\t\t\t\t static initializer blocks hold the null lock");
	System.err.println(" -quiet\t\t\t\t don't print status messages");
	System.err.println(" -nowarn <category>\t\t turn off warning category");
	System.err.println(" -warn <category>\t\t turn on warning category");    
	System.err.println(" -warn_package <package>\t print warning from code in package");
	System.err.println(" -nowarn_package <package>\t turn off warnings from code in package");
	System.err.println(" -trace_error \t\t\t (for debugging)   ");
	System.err.println(" -ignoreAnnFile <file>\t\t\t ignore annotations at locs in file");
	System.err.println(" -suggest\t\t\t\t suggest fixes in warning messages");
    }
    
    
    /***************************************************
     *                                                 *
     * Option processing:			       *
     *                                                 *
     ***************************************************/
    
    /**
     ** Process next tool option. <p>
     **
     ** See <code>Tool.processOption</code> for the complete
     ** specification of this routine.<p>
     **/
    //# guarded_by foo
    public int processOption(String option, String[] args, int offset)
    { 
	if (option.equals("-pjt")) {
	    pjt = true;
	    return offset;
	}
	if (option.equals("-ihl")) {
	    ihl = true;
	    return offset;
	}
	if (option.equals("-ihnl")) {
	    ihnl = true;
	    return offset;
	}
	if (option.equals("-prg")) {
	    prg = true;
	    return offset;
	}
	if (option.equals("-agt")) {
	    agt = true;
	    return offset;
	}
	if (option.equals("-noho")) {
	    noho = true;
	    return offset;
	}
	if (option.equals("-wall")) {
	    wall = true;
	    NoWarn.reset();
	    return offset;
	}
	if (option.equals("-pun")) {
	    pun = true;
	    return offset;
	}
	if (option.equals("-chl")) {
	    chl = true;
	    return offset;
	}
	if (option.equals("-dts")) {
	    dts = true;
	    return offset;
	}	 
	if (option.equals("-suggest")) {
	    suggest = true;
	    return offset;
	}	
	if (option.equals("-trace_error")) {
	    tse = true;
	    return offset;
	}
	if (option.equals("-quiet")) {
	    quiet = true;
	    return offset;
	} else if (option.equals("-nowarn")) {
	    if (offset>=args.length) {
		usage();
		System.exit(usageError);
	    }
	    int tag = NoWarn.toNoWarnTag(args[offset]);
	    if (tag==0) {
		System.err.println(name() + ": '" + args[offset]
				   + "' is not a legal warning category");
		System.exit(usageError);
	    }
	    NoWarn.setChkStatus(tag, TagConstants.CHK_AS_ASSUME);
	    return offset+1;
	} else if (option.equals("-warn")) {
	    if (offset>=args.length) {
		usage();
		System.exit(usageError);
	    }
	    int tag = NoWarn.toNoWarnTag(args[offset]);
	    if (tag==0) {
		System.err.println(name() + ": '" + args[offset]
				   + "' is not a legal warning category");
		System.exit(usageError);
	    }
	    NoWarn.setChkStatus(tag, TagConstants.CHK_AS_ASSERT);
	    return offset+1;
	} else if (option.equals("-nowarn_package")) {
	    if (offset>=args.length) {
		usage();
		System.exit(usageError);
	    }
	    NoWarn.setPackageStatus(args[offset], TagConstants.CHK_AS_ASSUME);
	    return offset+1;
	} else if (option.equals("-warn_package")) {
	    if (offset>=args.length) {
		usage();
		System.exit(usageError);
	    }
	    NoWarn.setPackageStatus(args[offset], TagConstants.CHK_AS_ASSERT);
	    return offset+1;
	} else if (option.equals("-ignoreAnnFile")) {
	    if (offset >= args.length) {
		badOptionUsage("-ignoreAnnFile expects a file parameter");
	    }
	    ignoreAnnSet = new Set(readFile(args[offset]).elements());
	    // System.out.println("Ignore set: "+ignoreAnnSet+"\n");
	    return offset+1;
	}
	
	return super.processOption(option, args, offset);
    }
    
    private Vector readFile(String filename) {
	Vector r = new Vector();
	StringBuffer s = new StringBuffer();
	try {
	    Reader R = new BufferedReader(new InputStreamReader(new FileInputStream(filename)));
	    int c;
	    do {
		while( (c=R.read())!= -1 && c != '\n' ) {
		    s.append( (char)c );
		}
		// Delete from 3rd space on
		String st = s.toString();
		int i=st.indexOf(' ');
		if( i != -1 ) i=st.indexOf(' ',i+1);
		if( i != -1 ) i=st.indexOf(' ',i+1);
		if( i != -1 ) st=st.substring(0,i);
		r.addElement( st );
		s.setLength(0);
	    } while( c != -1 );
	    return r;
        } catch(IOException e) {
	  throw new RuntimeException("IOException: " + e);
	}
    }

    
    private void badOptionUsage(String s) {
      System.err.println(s);
      System.err.println();
      usage();
      System.exit(usageError);
    }

    /***************************************************
     *                                                 *
     *  Front-end setup:		               *
     *                                                 *
     ***************************************************/
    
    /*
      public StandardTypeReader makeStandardTypeReader(String path,
      PragmaParser P) {
      return RccTypeReader.make(path, P);
      }
    */
    
    public javafe.parser.PragmaParser makePragmaParser() {
	return new rcc.parser.RccPragmaParser();
    }
    
    
    public PrettyPrint makePrettyPrint() {
	DelegatingPrettyPrint p = new RccPrettyPrint();
	p.del = new StandardPrettyPrint(p);
	return p;
    }
    

    public javafe.tc.TypeCheck makeTypeCheck() {
	return new rcc.tc.TypeCheck();
    }
    
    
    /**
     ** Override SrcTool.notify to ensure all lexicalPragmas get
     ** registered as they are loaded.
     **/
    public void notify(CompilationUnit justLoaded) {
	super.notify(justLoaded);
	
	NoWarn.registerNowarns(justLoaded.lexicalPragmas);
    }
    
    
    /***************************************************
     *                                                 *
     * Main processing code:			       *
     *                                                 *
     ***************************************************/
    
    /**
     ** Start up an instance of this tool using command-line arguments
     ** <code>args</code>. <p> 
     **
     ** This is the main entry point for the <code>rcc</code>
     ** command.<p>
     **/
    //@ requires elemsnonnull(args)
    public static void main(String[] args) {
	
	new rcc.tc.Types();
	
	
	javafe.SrcTool t = new Main();
	
	// Disallow the -avoidSpec option:
	t.allowAvoidSpec = false;
	
	t.run(args);

	if (pun) {
	    NoWarn.displayUntriggeredNowarns();
	}
	
    }
    
    
    /***************************************************
     *                                                 *
     * SrcTool-instance specific processing:	       *
     *                                                 *
     ***************************************************/
    
    
    /**
     ** Hook for any work needed before <code>handleCU</code> is called
     ** on each <code>CompilationUnit</code> to process them.
     **/
    public void preprocess() {
	if (!quiet)
	    System.out.println("Rcc version " + version);
	commandLineFiles = (Vector)loaded.clone();
	/*	for (int i = 0; i < commandLineFiles.size(); i++)
		System.out.println(commandLineFiles.elementAt(i)); */
    }
    
    /**
     ** Hook for any work needed after <code>handleCU</code> has been called
     ** on each <code>CompilationUnit</code> to process them.
     **/
    public void postprocess() {
    }
    
    /**
     ** This method is called on each <code>CompilationUnit</code>
     ** that this tool processes.  This method overrides the implementation
     ** given in the superclass, adding a couple of lines before the
     ** superclass implementation is called.
     **/
    public void handleCU(CompilationUnit cu) {
				// NoWarn.setStartLine(startLine, cu);
	
        // UniqName.setDefaultSuffixFile(cu.getStartLoc());
	super.handleCU(cu);
	
	startLine = -1;		// StartLine applies only to first CU
    }
    
    
    /**
     ** This method is called by SrcTool on the TypeDecl of each
     ** outside type that SrcTool is to process. <p>
     **
     ** In addition, it calls itself recursively to handle types
     ** nested within outside types.<p>
     **/
    public void handleTD(TypeDecl td) {
	TypeSig sig = TypeCheck.inst.getSig(td);
	if (sig.getTypeDecl().specOnly)	// do not process specs
	    return;
	
	if (Location.toLineNumber(td.getEndLoc()) < startLine)
	    return;
	
	
	long startTime = java.lang.System.currentTimeMillis();
	if (!quiet)
	    System.out.println("\n" + sig.toString() + " ...");
	
				// Do actual work:
	boolean aborted = processTD(td);
	
	if (!quiet)
	    System.out.println("  [" + timeUsed(startTime)
			       + " total]"
			       + (aborted ? " (aborted)" : "") );
	
				/*
				 * Handled any nested types:  [1.1]
				 */
	TypeDecl decl = sig.getTypeDecl();
	for (int i=0; i<decl.elems.size(); i++) {
	    if (decl.elems.elementAt(i) instanceof TypeDecl)
		handleTD((TypeDecl)decl.elems.elementAt(i));
	}
    }
    
    
    /**
     ** Run all the requested stages on a given TypeDecl;
     ** return true if we had to abort. <p>
     **
     ** Precondition: td is not from a binary file.<p>
     **/
    private boolean processTD(TypeDecl td) {

	int errorCount = ErrorSet.errors;
	TypeSig sig = TypeCheck.inst.getSig(td);
	sig.typecheck();
	if (pjt) {
	    // Create a pretty-printer that shows types
	    DelegatingPrettyPrint p = new javafe.tc.TypePrint();
	    
	    // p.del = new RccPrettyPrint(p, new StandardPrettyPrint(p));
	    p.del = new StandardPrettyPrint(p);
	    
	    if (rcc.tc.TypeSig.defaultInstantiationDecoration.get(sig)!=null) {
		td = ((TypeSig)rcc.tc.TypeSig.defaultInstantiationDecoration.get(sig)).getTypeDecl();
	    }
	    
	    System.out.println("\n**** Source code with types:");
	    p.print(System.out, 0, td);
	}
	

	return false;
    }
    
    
    
    /***************************************************
     *                                                 *
     * Misc. Utility routines:			       *
     *                                                 *
     ***************************************************/
    
    /**
     ** Compute the time used from a start time to now, then return it
     ** in a user readable form.
     **/
    /*@ensures RES != null*/
    String timeUsed(long startTime) {
	long delta = java.lang.System.currentTimeMillis() - startTime;
	
	return (delta/1000.0) + " s";
    }
    
}















