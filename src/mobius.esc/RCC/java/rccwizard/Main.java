/* Copyright 2000, 2001, Compaq Computer Corporation */

package rccwizard;

import javafe.Options;
import javafe.ast.CompilationUnit;
import javafe.ast.TypeDecl;
import javafe.tc.TypeCheck;
import javafe.tc.TypeSig;

/**
 * * Top level control module for ESC for Java.
 * <p> * * This class (and its superclasses) handles parsing *
 * <code>escjava</code>'s command-line arguments and orchestrating the *
 * other pieces of the front end and escjava to perform the requested *
 * operations.
 * <p> * *
 * 
 * @see javafe.Tool *
 * @see javafe.SrcTool
 */

public class Main extends javafe.SrcTool {

    public static Main inst = null;

    public Main() {
        // assert (inst == null);
        inst = this;
    }

    /** Our version number * */
    public final String version = "0.0 based on fwdwizard 1.0.0, 14 July 1999";

    // === Options processing ===
    /**
     * rgrig: The following two functions follow the ESC/Java2 convention.
     */

    public/* @ non_null */Options makeOptions() {
        return RccOptions.get();
    }

    /** My name is... */
    public String name() {
        return "rccwizard annotation generator";
    }

    /**
     * * This method is called on each <code>CompilationUnit</code> * that
     * this tool processes. This method overrides the implementation * given in
     * the superclass, adding a couple of lines before the * superclass
     * implementation is called.
     */
    public void handleCU(CompilationUnit cu) {
        super.handleCU(cu);
    }

    /***************************************************************************
     * * Front-end setup: * *
     **************************************************************************/

    public javafe.parser.PragmaParser makePragmaParser() {
        return new rcc.parser.RccPragmaParser();
    }

    /*
     * public javafe.tc.TypeCheck makeTypeCheck() { return new
     * rcc.tc.TypeCheck(); }
     */

    /***************************************************************************
     * * Main processing code: * *
     **************************************************************************/

    /**
     * * Start up an instance of this tool using command-line arguments *
     * <code>args</code>.
     * <p> * * This is the main entry point for the <code>escjava</code> *
     * command.
     * <p>
     */
    // @ requires elemsnonnull(args)
    public static void main(String[] args) {
        // new rcc.tc.Types();
        // System.out.println ("main,"+args[2]);
        javafe.SrcTool t = new Main();

        t.run(args);
    }

    /***************************************************************************
     * * SrcTool-instance specific processing: * *
     **************************************************************************/

    /**
     * * This method is called by SrcTool on the TypeDecl of each * outside type
     * that SrcTool is to process.
     * <p> * * In addition, it calls itself recursively to handle types * nested
     * within outside types.
     * <p>
     */
    public void handleTD(TypeDecl td) {
        // System.out.println ("handleTD");

        TypeSig sig = TypeCheck.inst.getSig(td);
        sig.typecheck();

        AnnotationVisitor v = new AnnotationVisitor();
        td.accept(v);
    }
}
