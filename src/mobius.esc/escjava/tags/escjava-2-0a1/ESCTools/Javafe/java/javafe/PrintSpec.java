/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe;


import java.util.Vector;

import javafe.ast.*;
import javafe.tc.*;
import javafe.util.*;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.*;

import java.util.StringTokenizer;

/**
 * <code>PrintSpec</code> print specs for class files.
 */

public class PrintSpec extends SrcTool {

    public String name() { return "PrintSpec"; }


    /***************************************************
     *                                                 *
     * Keeping track of loaded CompilationUnits:       *
     *                                                 *
     **************************************************/

    class PrintSpecPrettyPrint extends StandardPrettyPrint {

		public void printnoln(OutputStream o, int ind, TypeDecl d) {
		    if (d != null && d.getTag() == javafe.ast.TagConstants.CLASSDECL) {
				ClassDecl cd = (ClassDecl)d;
				if (Character.isDigit((cd.id.toString().charAt(0)))) {
				    System.out.println("---> skipping anonymous inner class");
				    return;
				}
		    }
		    super.printnoln(o, ind, d);
		}
    }	    

    public void setup() { 
		super.setup();
		PrettyPrint.inst = new PrintSpecPrettyPrint();
    }

    /***************************************************
     *                                                 *
     * Main processing code:			       *
     *                                                 *
     **************************************************/



    //@ requires \nonnullelements(args)
    public static void main(String[] args) {
		Tool t = new PrintSpec();
		int result = t.run(args);
		if (result != 0) System.exit(result);
    }



    //@ ensures \nonnullelements(\result)
    //@ ensures \result != null
    public String[] FQNpackage(/*@ non_null */ String s) {
        StringTokenizer st = new StringTokenizer(s, ".", false);
        int len = st.countTokens();
		if (len < 1) {
		    return new String[0];
		}
        String array[] = new String[len-1];
        for (int i = 0; i < len-1; i++) {
            array[i] = st.nextToken();
        }
        return array;
    } 

    //@ ensures \result != null
    public String FQNname(/*@ non_null */ String s) {
	 	return s.substring(s.lastIndexOf(".") + 1);
    } 
    

    //@ requires \nonnullelements(P)
    private String makeDirTree(/*@ non_null */ String P[]) {
        String s = ".";
        for (int i = 0; i < P.length; i++) {
            s = s + "/" + P[i];
            java.io.File f = new File(s);
            if (!f.exists()) f.mkdir();            
        }
        return s;
    }
    
    public void loadAndPrintSpec(/*@ non_null */ String s) {
	String P[] = FQNpackage(s);
	String T = FQNname(s);
	TypeSig sig = OutsideEnv.lookup(P, T);
	if (sig == null) {
	    System.out.println("Can't find " + s);
	    return;
	}
	String path = makeDirTree(P);
	String outFile = T + ".spec";
	String filename = path + "/" +  outFile;
	System.out.println("generating " + filename + "...");
	FileOutputStream fos = null;
	try {
	    fos = new FileOutputStream(filename);
	} catch (Exception e) {
	    ErrorSet.fatal(e.getMessage());
	}
	PrettyPrint.inst.print(fos, sig.getCompilationUnit());
    }


    public final void frontEndToolProcessing(String[] args, int offset) {
	/*
	 * At this point, all options have already been processed and
	 * the front end has been initialized.
	 */

	// Set up to receive CompilationUnit-loading notification events:
	OutsideEnv.setListener(this);

	/*
	 * Load in each source file:
	 */
	for (; offset<args.length; offset++) {
	    this.loadAndPrintSpec(args[offset]);
	}
	
	/* load in source files from supplied file name */
	for (int i = 0; i < argumentFileNames.size(); i++) {
	    String argumentClassName = (String)argumentFileNames.elementAt(i);
	    try {
		BufferedReader in = new BufferedReader(
					    new FileReader(argumentClassName));
		String s;
		while ((s = in.readLine()) != null) {
		    // allow blank lines in files list
		    if (!s.equals("")) {
			this.loadAndPrintSpec(s);
		    }
		}
	    } catch (IOException e) {
		ErrorSet.fatal(e.getMessage());
	    }
	}
    }
}
