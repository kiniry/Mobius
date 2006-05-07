/* Copyright 2000, 2001, Compaq Computer Corporation */

package rccwizard;


import java.util.Enumeration;
import java.util.Hashtable;

import javafe.ast.*;

import javafe.reader.StandardTypeReader;

import javafe.parser.PragmaParser;

import javafe.tc.TypeSig;
import javafe.tc.TypeCheck;

import javafe.util.*;


/**
 ** Top level control module for ESC for Java. <p>
 **
 ** This class (and its superclasses) handles parsing
 ** <code>escjava</code>'s command-line arguments and orchestrating the
 ** other pieces of the front end and escjava to perform the requested
 ** operations.<p>
 **
 ** @see javafe.Tool
 ** @see javafe.SrcTool
 **/

public class Main extends javafe.SrcTool {

     /** Our version number **/
     public final String version = "0.0 based on fwdwizard 1.0.0, 14 July 1999";

    public static boolean pmnr  = false; //  public methods have no requires
    public static boolean readonly  = false; //  only insert readonly annot.
    public static boolean guessnull  = true; 
 

    /***************************************************
     *                                                 *
     * Generating an options message:                       *
     *                                                 *
     ***************************************************/

    /**
     ** Return the name of this tool.  E.g., "ls" or "cp".<p>
     **
     ** Used in usage and error messages.<p>
     **/
    public String name() { return "rccwizard annotation generator"; }

    /**
     ** Print option option information to
     ** <code>System.err</code>. <p>
     **/
    public void showOptions() {
        System.err.println(" -pmnr \t\t\t public methods cannot have requires clauses   ");
        System.err.println(" -noguessnull \t\t\t don't guess null as guarding lock  ");
        System.err.println(" -readonly \t\t\t only guess readonly annotations");
        super.showOptions();
    }

  
    /***************************************************
     *                                                 *
     * Option processing:                               *
     *                                                 *
     ***************************************************/


    /**
     ** Process next tool option. <p>
     **
     ** See <code>Tool.processOption</code> for the complete
     ** specification of this routine.<p>
     **/
    public int processOption(String option, String[] args, int offset) {
        if (option.equals("-pmnr")) {
            pmnr = true;
            return offset;
        } else if (option.equals("-readonly")) {
            readonly = true;
            return offset;
        } else if (option.equals("-noguessnull")) {
            guessnull = false;
            return offset;
        }
        return super.processOption(option, args, offset);
    }


    /**
     ** This method is called on each <code>CompilationUnit</code>
     ** that this tool processes.  This method overrides the implementation
     ** given in the superclass, adding a couple of lines before the
     ** superclass implementation is called.
     **/
    public void handleCU(CompilationUnit cu) {
        super.handleCU(cu);
    }
  
    /***************************************************
     *                                                 *
     *  Front-end setup:                               *
     *                                                 *
     ***************************************************/

    public javafe.parser.PragmaParser makePragmaParser() {
        return new rcc.parser.RccPragmaParser();
    }
    /*
      public javafe.tc.TypeCheck makeTypeCheck() {
        return new rcc.tc.TypeCheck();
    }
    */
    
    /***************************************************
     *                                                 *
     * Main processing code:                               *
     *                                                 *
     ***************************************************/

    /**
     ** Start up an instance of this tool using command-line arguments
     ** <code>args</code>. <p> 
     **
     ** This is the main entry point for the <code>escjava</code>
     ** command.<p>
     **/
    //@ requires elemsnonnull(args)
    public static void main(String[] args) {
        //new rcc.tc.Types();
        //System.out.println ("main,"+args[2]);
        javafe.SrcTool t = new Main();

        t.run(args);
    }


    /***************************************************
     *                                                 *
     * SrcTool-instance specific processing:               *
     *                                                 *
     ***************************************************/

    /**
     ** This method is called by SrcTool on the TypeDecl of each
     ** outside type that SrcTool is to process. <p>
     **
     ** In addition, it calls itself recursively to handle types
     ** nested within outside types.<p>
     **/
    public void handleTD(TypeDecl td) {
        //System.out.println ("handleTD");
        
      TypeSig sig = TypeCheck.inst.getSig(td);
      sig.typecheck();

      AnnotationVisitor v = new AnnotationVisitor();
      td.accept(v);
    }
}
