/* Copyright 2000, 2001, Compaq Computer Corporation */

// SNF Mon Jun 28 17:28:37 1999
// based on main from esc
package rcc;


import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;
import java.io.*;

import javafe.Options;
import javafe.ast.*;

import rcc.ast.*;
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
    
    
    // === Options processing ===
    /**
     * rgrig: The following two functions follow the ESC/Java2 convention.
     */
    
    
    public /*@ non_null */ Options makeOptions() {
        return new RccOptions();
    }
    
    public RccOptions options() {
        return (RccOptions)options;
    }
    
    /**
     ** Return the name of this tool.  E.g., "ls" or "cp".<p>
     **
     ** Used in usage and error messages.<p>
     **/
    public String name() { return "rcc"; }
    

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
	
	
	Main t = new Main();
	
	t.run(args);

	if (t.options().pun) {
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
	if (!options().quiet)
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
	
	options().startLine = -1;		// StartLine applies only to first CU
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
	
	if (Location.toLineNumber(td.getEndLoc()) < options().startLine)
	    return;
	
	
	long startTime = java.lang.System.currentTimeMillis();
	if (!options().quiet)
	    System.out.println("\n" + sig.toString() + " ...");
	
				// Do actual work:
	boolean aborted = processTD(td);
	
	if (!options().quiet)
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
	if (options().pjt) {
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
    
}















