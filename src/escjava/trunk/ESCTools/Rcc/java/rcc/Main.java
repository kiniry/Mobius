/* Copyright 2000, 2001, Compaq Computer Corporation */

// SNF Mon Jun 28 17:28:37 1999
// based on main from esc
package rcc;

import java.util.Vector;

import javafe.Options;
import javafe.ast.CompilationUnit;
import javafe.ast.DelegatingPrettyPrint;
import javafe.ast.PrettyPrint;
import javafe.ast.StandardPrettyPrint;
import javafe.ast.TypeDecl;
import javafe.tc.TypeSig;
import javafe.util.Location;
import rcc.ast.NoWarn;
import rcc.ast.RccPrettyPrint;
import rcc.tc.TypeCheck;

/**
 * The main class of the <tt>RCC</tt> tool.
 * 
 * @see javafe.SrcTool
 */

public class Main extends javafe.SrcTool {

    /** Our version number */
    public final String version = "1.0.0";

    public Vector commandLineFiles;

    public static Main inst = null;

    public Main() {
        inst = this;
    }

    // === Options processing ===
    // The following two functions follow the ESC/Java2 convention.
    
    //@Override
    public/* @ non_null */Options makeOptions() {
        return RccOptions.get();
    }

    /**
     * @return "rcc", which is the name of this tool.
     */
    //@Override
    public String name() {
        return "RCC";
    }

    // === Front-end setup ===
    // The following are overrides of template methods in
    // <code>javafe.SrcTool</code>.

    //@Override
    public javafe.parser.PragmaParser makePragmaParser() {
        return new rcc.parser.RccPragmaParser();
    }

    //@Override
    public PrettyPrint makePrettyPrint() {
        DelegatingPrettyPrint p = new RccPrettyPrint();
        p.setDel(new StandardPrettyPrint(p));
        return p;
    }

    //@Override
    public javafe.tc.TypeCheck makeTypeCheck() {
        return rcc.tc.TypeCheck.get();
    }

    /**
     * Make sure all lexical pragmas get registered as they are loaded.
     */
    //@Override
    public void notify(CompilationUnit justLoaded) {
        super.notify(justLoaded);
        NoWarn.registerNowarns(justLoaded.lexicalPragmas);
    }

    // === Main processing code ===

    /**
     * Start up an instance of this tool using command-line arguments
     * <code>args</code>.
     * 
     * This is the main entry point for the <tt>RCC</tt> tool.
     */
    // @ requires elemsnonnull(args)
    public static void main(String[] args) {
        // Enables overriding of static methods.
        new rcc.tc.Types();

        Main t = new Main();

        t.run(args);

        if (RccOptions.get().pun) {
            NoWarn.displayUntriggeredNowarns();
        }
        
        /* DBG: See the ALL code that gets processed.
        for (int i = 0; i < t.loaded.size(); ++i) {
            CompilationUnit cu = (CompilationUnit)t.loaded.get(i);
            PrettyPrint.inst.print(System.out, cu);
        }
        */
    }

    // === [SrcTool] specific processing ===

    /**
     * Hook for any work needed before <code>handleCU</code> is called on each
     * <code>CompilationUnit</code> to process them.
     */
    //@Override
    public void preprocess() {
        if (!RccOptions.get().quiet) {
            System.out.println(name() + " version " + version);
        }
        commandLineFiles = (Vector) loaded.clone();
    }

    /**
     * This method is called on each <code>CompilationUnit</code> that this
     * tool processes. This method overrides the implementation given in the
     * superclass, adding a couple of lines before the superclass implementation
     * is called.
     */
    /*
     * rgrig: does it do anything useful? public void handleCU(CompilationUnit
     * cu) { // NoWarn.setStartLine(startLine, cu); //
     * UniqName.setDefaultSuffixFile(cu.getStartLoc()); super.handleCU(cu);
     * 
     * RccOptions.get().startLine = -1; // StartLine applies only to first CU }
     */

    /**
     * This method is called by <code>SrcTool</code> on the
     * <code>TypeDecl</code> of each outside type that <code>SrcTool</code>
     * is to process. In addition, it calls itself recursively to handle types
     * nested within outside types.
     * <p>
     */
    //@Override
    public void handleTD(TypeDecl td) {
        TypeSig sig = TypeCheck.inst.getSig(td);
        if (sig.getTypeDecl().specOnly) // do not process specs
            return;

        if (Location.toLineNumber(td.getEndLoc()) < RccOptions.get().startLine)
            return;

        // Do actual work:
        processTD(td);

        /*
         * Handled any nested types: [1.1]
         */
        TypeDecl decl = sig.getTypeDecl();
        for (int i = 0; i < decl.elems.size(); i++) {
            if (decl.elems.elementAt(i) instanceof TypeDecl)
                handleTD((TypeDecl) decl.elems.elementAt(i));
        }
    }

    /**
     * Run all the requested stages on a given <code>TypeDecl</code>.
     * 
     * @pre <code>td</code> is not from a binary file.
     * @return <code>true</code> iff we had to abort.
     */
    private boolean processTD(TypeDecl td) {
        TypeSig sig = TypeCheck.inst.getSig(td);
        sig.typecheck();
        if (RccOptions.get().pjt) {
            // Create a pretty-printer that shows types
            DelegatingPrettyPrint p = new javafe.tc.TypePrint();

            // p.del = new RccPrettyPrint(p, new StandardPrettyPrint(p));
            p.setDel(new StandardPrettyPrint(p));

            System.out.println("\n**** Source code with types:");
            p.print(System.out, 0, td);
        }

        return false;
    }

}
