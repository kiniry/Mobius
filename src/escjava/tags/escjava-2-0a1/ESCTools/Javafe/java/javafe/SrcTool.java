/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe;

import java.util.Vector;
import java.util.Enumeration;
import java.util.Iterator;
import java.util.ArrayList;

import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;
import javafe.genericfile.GenericFile;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;

/**
 * <code>SrcTool</code> is an abstract class for tools that use
 * our Java front end to process the <code>CompilationUnit</code>s
 * found in source files. <p>
 *
 * It adds to <code>FrontEndTool</code> code for processing a series of
 * source files specified on the command line.  
 * 
 * If processRecursively is set, then files are processed
 * recursively.  (I.e., files loaded in the course of processing one
 * file are also processed.)<p>
 *
 * The remaining processing, if any, is front-end-tool specific.<p>
 */

public abstract class SrcTool extends FrontEndTool implements Listener
{

    /**
     * Contains the filenames that contain the names of the sources on which
     * to invoke the tool.
     */
    protected final Vector argumentFileNames = new Vector();
    //@ invariant argumentFileNames.elementType == \type(String);
    //@ invariant !argumentFileNames.containsNull;
    //@ invariant argumentFileNames.owner == this



    /***************************************************
     *                                                 *
     * Keeping track of loaded CompilationUnits:       *
     *                                                 *
     **************************************************/

    /**
     * A list of all the <code>CompilationUnit</code>s we have loaded
     * so far.  This list is extended automatically at the end as new
     * <code>CompilationUnit</code>s are loaded using notification from
     * <code>OutsideEnv</code>.
     */
    //@ invariant loaded!=null 
    //@ invariant loaded.elementType == \type(CompilationUnit)
    //@ invariant !loaded.containsNull
    //@ invariant loaded.owner == this
    public Vector loaded = new Vector();

    //@ invariant loaded != argumentFileNames;

    public SrcTool() {
		super();

        //@ set argumentFileNames.elementType = \type(String);
        //@ set argumentFileNames.containsNull = false;
		//@ set argumentFileNames.owner = this
	
		//@ set loaded.elementType = \type(CompilationUnit)
		//@ set loaded.containsNull = false
		//@ set loaded.owner = this
    }


    /**
     * Add a <code>CompilationUnit</code> to <code>loaded</code>. <p>
     *
     * This should only be called by <code>OutsideEnv</code> using the
     * <code>Listener</code> interface.<p>
     */
    public void notify(CompilationUnit justLoaded) {
		loaded.addElement(justLoaded);
    }


    /***************************************************
     *                                                 *
     * Main processing code:			       *
     *                                                 *
     **************************************************/

    public Options makeOptions() {
    	return new SrcToolOptions();
    }

    public int processOptions(String[] args) throws UsageError {
        options().argumentFileNames = argumentFileNames;
        return super.processOptions(args);
    }
    
    private static SrcToolOptions options() { 
    	return (SrcToolOptions)options;
    }

    /**
     * Main processing loop for <code>SrcTool</code>. <p>
     *
     * The remaining arguments are <code>args[offset]</code>,
     * <code>args[offset+1]</code>, ...<p>
     *
     * This method calls preload, loadAllFiles, preprocess, handleAllCU, postprocess.
     */
    public void frontEndToolProcessing(String[] args, int offset) {
	/*
	 * At this point, all options have already been processed and
	 * the front end has been initialized.
	 */

	// Set up to receive CompilationUnit-loading notification events:
	OutsideEnv.setListener(this);
	
        preload();
	
        loadAllFiles(offset,args);
	
	OutsideEnv.avoidSpec = options().avoidSpec;
	if (options().processRecursively)
	    OutsideEnv.avoidSpec = true;

	// Do any tool-specific pre-processing:
	preprocess();
	
        handleAllCUs();
	
	// Do any tool-specific post-processing:
	postprocess();
    }


    /***************************************************
     *                                                 *
     * SrcTool-instance specific processing:	       *
     *                                                 *
     **************************************************/

    public void loadAllFiles(int offset, String[] args) {
    	/*
	 * Load in each source file:
	 */
	for (; offset<args.length; offset++)
	    OutsideEnv.addSource(args[offset]);

	loadPackages(options.packagesToProcess);

	/* load in source files from supplied file name */
	for (int i = 0; i < argumentFileNames.size(); i++) {
	    String argumentFileName = (String)argumentFileNames.elementAt(i);
	    try {
		BufferedReader in = new BufferedReader(
				    new FileReader(argumentFileName));
		String s;
		while ((s = in.readLine()) != null) {
		    // allow blank lines in files list
		    if (!s.equals("")) {
			OutsideEnv.addSource(s);
		    }
		}
	    } catch (IOException e) {
		ErrorSet.fatal(e.getMessage());
	    }
	}
    }

    public void loadPackages(ArrayList packagesToProcess) {
	Iterator i = packagesToProcess.iterator();
	while (i.hasNext()) {
	    String p = (String)i.next();
	    String[] pa = javafe.filespace.StringUtil.parseList(p,'.');
	    OutsideEnv.addSources(pa);
	}
    }

    /** Iterates, calling handleCU for each loaded CU.
     */	
    public void handleAllCUs() {
	/*
	 * Call handleCU on the resulting loaded CompilationUnits.
	 *
	 * If processRecursively is true, then continue calling handleCU
	 * on loaded CompilationUnits that have not had handleCU called
	 * on them in the order they were loaded until no such
	 * CompilationUnits remain.  (handleCU may load CompilationUnits
	 * indirectly.)
	 */
	int i=0;
	for (int end=loaded.size(); i<end; i++) {
	    handleCU((CompilationUnit)loaded.elementAt(i));
	    if (options().processRecursively) {
			Assert.notFalse(OutsideEnv.avoidSpec == true);
			end = loaded.size();
	    }
	}
    }
	 
    /**
     * Hook for any work needed before any files are loaded.
     */
    public void preload() {}
    
    /**
     * Hook for any work needed after files are loaded
     * but before <code>handleCU</code> is called
     * on each <code>CompilationUnit</code> to process them.
     */
    public void preprocess() {}

    /**
     * Hook for any work needed after <code>handleCU</code> has been called
     * on each <code>CompilationUnit</code> to process them.
     */
    public void postprocess() {}


    /**
     * This method is called on each <code>CompilationUnit</code>
     * that this tool processes. <p>
     *
     * The default implementation is simply to call
     * <code>handleTD</code> on each <code>TypeDecl</code> present in
     * cu.  It is intended that subclassers override this method.<p>
     */
    //@ requires cu!=null
    public void handleCU(CompilationUnit cu) {
		// Iterate over all the TypeDecls representing outside types in cu:
		TypeDeclVec elems = cu.elems;
		for (int i=0; i<elems.size(); i++) {
		    TypeDecl d = elems.elementAt(i);
	
		    handleTD(d);
		}
    }


    /**
     * This method is called on the TypeDecl of each
     * outside type that SrcTool is to process. <p>
     */
    //@ requires td!=null
    public void handleTD(TypeDecl td) {}

}
