/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;
import java.util.ArrayList;
import java.io.*;

import javafe.ast.*;
import escjava.ast.*;
import escjava.ast.EscPrettyPrint;
import escjava.ast.TagConstants;
import escjava.ast.Modifiers;

import escjava.backpred.FindContributors;
import escjava.AnnotationHandler;

import javafe.reader.StandardTypeReader;
import escjava.reader.EscTypeReader;

import javafe.parser.PragmaParser;
import javafe.tc.OutsideEnv;
import javafe.genericfile.GenericFile;

import escjava.sp.*;

import escjava.translate.*;
import escjava.pa.*;

import javafe.tc.TypeSig;
import escjava.tc.TypeCheck;

import escjava.prover.*;

import javafe.util.*;

/**
 * Top level control module for ESC for Java.
 *
 * <p>This class (and its superclasses) handles parsing
 * <code>escjava</code>'s command-line arguments and orchestrating the
 * other pieces of the front end and escjava to perform the requested
 * operations.<p>
 *
 * @see javafe.Tool
 * @see javafe.SrcTool
 */

public class Main extends javafe.SrcTool
{
    /** Our version number */
    //public final static String version = "(Nijmegen/Kodak) 1.3, 2003";
    public final static String version = Version.VERSION;


    public AnnotationHandler annotationHandler = new AnnotationHandler();

    // Convenience copy of options().stages
    public int stages;

    /**
     * Return the name of this tool.  E.g., "ls" or "cp".<p>
     *
     * Used in usage and error messages.<p>
     */
    public String name() { return "escjava"; }

    public javafe.Options makeOptions() { return new Options(); }
    
    public static Options options() { return (Options)options; }

    // Front-end setup

    /**
     * Returns the Esc StandardTypeReader, EscTypeReader.
     */
    public StandardTypeReader makeStandardTypeReader(String path,
				String sourcePath,
                             PragmaParser P) {
        return EscTypeReader.make(path, sourcePath, P, annotationHandler);
    }

    /**
     * Returns the EscPragmaParser.
     */
    public javafe.parser.PragmaParser makePragmaParser() {
        return new escjava.parser.EscPragmaParser();
    }

    /**
     * Returns the pretty printer to set
     * <code>PrettyPrint.inst</code> to.
     */
    public PrettyPrint makePrettyPrint() {
        DelegatingPrettyPrint p = new EscPrettyPrint();
        p.del = new StandardPrettyPrint(p);
        return p;
    }

    /**
     * Called to obtain an instance of the javafe.tc.TypeCheck class
     * (or a subclass thereof). May not return <code>null</code>.  By
     * default, returns <code>javafe.tc.TypeCheck</code>.
     */
    public javafe.tc.TypeCheck makeTypeCheck() {
        return new escjava.tc.TypeCheck();
    }


    /**
     * Override SrcTool.notify to ensure all lexicalPragmas get
     * registered as they are loaded.
     */
    public void notify(CompilationUnit justLoaded) {
        super.notify(justLoaded);
    
        NoWarn.registerNowarns(justLoaded.lexicalPragmas);
    
        if (options().printCompilationUnitsOnLoad) {
            String pkgName = justLoaded.pkgName.printName();
            String filename = Location.toFileName(justLoaded.loc);
            System.out.println("LOADED: " + pkgName + " " + filename);
        }
    }


    // Main processing code

    /**
     * Start up an instance of this tool using command-line arguments
     * <code>args</code>. <p>
     *
     * This is the main entry point for the <code>escjava</code>
     * command.<p>
     */
    //@ requires \nonnullelements(args)
    public static void main(String[] args) {
	int exitcode = compile(args);
	if (exitcode != 0) System.exit(exitcode);
    }

    public Main() {
        clear(); // resets any static variables left from a previous instantiation
    }

    boolean keepProver = false;

    public void clear() {
        super.clear();
        gctranslator = new Translate();
        if (!keepProver) prover = null;
        // restore ordinary checking of assertions
        NoWarn.useGlobalStatus = false; 
	NoWarn.setAllChkStatus(TagConstants.CHK_AS_ASSERT);
        // Disallow the -avoidSpec option:
        javafe.SrcToolOptions.allowAvoidSpec = false; 

    }

    public static int compile(String[] args) {
        try {
            Main t = new Main();
            int result = t.run(args);
            return result;
        } catch (OutOfMemoryError oom) {
            Runtime rt = Runtime.getRuntime();
            long memUsedBytes = rt.totalMemory() - rt.freeMemory();
            System.out.println("java.lang.OutOfMemoryError (" + memUsedBytes +
                                " bytes used)");
            //oom.printStackTrace(System.out);
            return outOfMemoryExitCode;
        }
    }


    // SrcTool-instance specific processing

    /**
     * Our Simplify instance, or null iff stages < 6.
     */
    public static Simplify prover = null;
    //@ invariant (prover == null) == (stages<6)

    /** An instance of the GC->VC translator */
    public static Translate gctranslator = new Translate();

    /**
     * Override setup so can issue version # as soon as possible (aka,
     * just after decode options so know if -quiet or -testMode issued or not).
     */
    public void setup() {
        stages = options().stages;
        super.setup();
        
        if (!options().quiet)
            System.out.println("ESC/Java version " + 
                (options().testMode?"VERSION":version));
    }

    /**
     * Hook for any work needed before <code>handleCU</code> is called
     * on each <code>CompilationUnit</code> to process them.
     */
    public void preprocess() {

	if (ErrorSet.fatals > 0) {
	    ErrorSet.fatal(null);
        }
        
        // call our routines to run the constructor inlining experiment
        if (options().inlineConstructors)
            InlineConstructor.inlineConstructorsEverywhere(loaded);
            
            
        if (6 <= stages || options().predAbstract) {
            long startTime = java.lang.System.currentTimeMillis();
            if (!keepProver || prover == null) prover = new Simplify();
            
            if (!options().quiet)
                System.out.println("  Prover started:" + timeUsed(startTime));
        }
        
        if (prover != null) {
            escjava.backpred.BackPred.genUnivBackPred(prover.subProcessToStream());
            prover.sendCommands("");
        }
    
    }

    /**
     * A wrapper for opening output files for printing.
     */
    private PrintStream fileToPrintStream(String dir, String fname) {
        File f = new File(dir, fname);
        try {
            return new PrintStream(new FileOutputStream(f));
        } catch (IOException e) {
            javafe.util.ErrorSet.fatal(e.getMessage());
            return null;  // unreachable
        }
    }

    /**
     * Hook for any work needed after <code>handleCU</code> has been
     * called on each <code>CompilationUnit</code> to process them.
     */
    public void postprocess() {

        // If we are in the Houdini context (guardedVC is true), output
        // the association of file numbers to their names.
        // Also, dump out a list of guard variable names.
        if (options().guardedVC) {
            PrintStream o = fileToPrintStream(options().guardedVCDir, options().guardedVCFileNumbers);
            Vector v = LocationManagerCorrelatedReader.fileNumbersToNames();
            for(int i=0; i<v.size(); i++) o.println(i + " " + v.elementAt(i));
            o.close();

            o = fileToPrintStream(options().guardedVCDir, options().guardedVCGuardFile);
            Enumeration e = options().guardVars.elements();
            while (e.hasMoreElements()) {
                o.println((String)e.nextElement());
            }
            o.close();
        }

        if (prover != null && !keepProver) {
            prover.close();
            prover = null;
        }
    }

    /**
     * This method is called on each <code>CompilationUnit</code> that
     * this tool processes.  This method overrides the implementation
     * given in the superclass, adding a couple of lines before the
     * superclass implementation is called.
     */
    public void handleCU(CompilationUnit cu) {
	if (options().testRef) makePrettyPrint().print(System.out,cu);

        NoWarn.setStartLine(options().startLine, cu);

        UniqName.setDefaultSuffixFile(cu.getStartLoc());
	try {
	    super.handleCU(cu);
	} catch (FatalError e) {
	    // Errors are already reported
	    //ErrorSet.report("Aborted processing " + cu.sourceFile().getHumanName() + " because of fatal errors");
	}

        options().startLine = -1;        // StartLine applies only to first CU
    }


    /**
     * This method is called by SrcTool on the TypeDecl of each
     * outside type that SrcTool is to process.
     *
     * <p> In addition, it calls itself recursively to handle types
     * nested within outside types.
     */
    public void handleTD(TypeDecl td) {
        long startTime = currentTime();
        TypeSig sig = TypeCheck.inst.getSig(td);

        if (!options().quiet)
            System.out.println("\n" + sig.toString() + " ...");

	/* If something is on the command-line, presume we want to check it
	   as thoroughly as possible.
        if (sig.getTypeDecl().specOnly &&
		!options().checkSpecs) {    // do not process specs
	    // No bodies to process
	    if (!options().quiet) System.out.println("Skipping " + 
				sig.toString() + " - specification only");
            return;
	}
	*/

        if (Location.toLineNumber(td.getEndLoc()) < options().startLine)
            return;

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
     * Run all the requested stages on a given TypeDecl; return true
     * if we had to abort.
     *
     */
    //@ requires (* td is not from a binary file. *);
    private boolean processTD(TypeDecl td) {
        // ==== Start stage 1 ====

        /*
         * Do Java type checking then print Java types if we've been
         * asked to:
         */
	long startTime = currentTime();
        int errorCount = ErrorSet.errors;
        TypeSig sig = TypeCheck.inst.getSig(td);
        sig.typecheck();
        NoWarn.typecheckRegisteredNowarns();
    

        if (options().pjt) {
            // Create a pretty-printer that shows types
            DelegatingPrettyPrint p = new javafe.tc.TypePrint();
            p.del = new EscPrettyPrint(p, new StandardPrettyPrint(p));

            System.out.println("\n**** Source code with types:");
            p.print(System.out, 0, td);
        }

        // Turn off extended static checking and abort if any errors
        // occured while type checking *this* TypeDecl:
        if (errorCount < ErrorSet.errors) {
            if (stages>1) {
                stages = 1;
                ErrorSet.caution("Turning off extended static checking " + 
                                     "due to type error(s)");
            }
            return true;
        }

        // ==== Start stage 2 ====
        if (stages<2)
            return false;
        

        // Generate the type-specific background predicate
        errorCount = ErrorSet.errors;
	if (Info.on) Info.out("[ Finding contributors for " + sig + "]");
        FindContributors scope = new FindContributors(sig);
        VcToString.resetTypeSpecific();
	if (Info.on) Info.out("[ Found contributors for " + sig + "]");
    
        if (options().guardedVC) {
            String locStr = UniqName.locToSuffix(td.locId);
            String fn = locStr + ".class." + options().guardedVCFileExt;
            File f = new File(options().guardedVCDir, fn);
            PrintStream o = fileToPrintStream(options().guardedVCDir, fn);
            o.println(options().ClassVCPrefix);
            o.println(td.id + "@" + locStr);
            o.print("\n(BG_PUSH ");
            escjava.backpred.BackPred.genTypeBackPred(scope, o);
            o.println(")");
            o.close();
        }

        if (prover != null) {
            PrintStream ps = prover.subProcessToStream();
            ps.print("\n(BG_PUSH ");
            escjava.backpred.BackPred.genTypeBackPred(scope, ps);
            ps.println(")");
            prover.sendCommands("");
        }

        // Turn off extended static checking and abort if any type errors
        // occured while generating the type-specific background predicate:
        if (errorCount < ErrorSet.errors) {
            stages = 1;
            ErrorSet.caution("Turning off extended static checking " + 
                             "due to type error(s)");
            return true;
        }

	if (options().testRef) makePrettyPrint().print(System.out,0,td);

        // ==== Start stage 3 ====
        if (3 <= stages) {

            LabelInfoToString.reset();
            InitialState initState = new InitialState(scope);
            LabelInfoToString.mark();

	    if (!options().quiet)
		System.out.println("    [" + timeUsed(startTime) + "]");

    
            // Process the elements of "td"; stage 3 continues into stages 4
            // and 5 inside processTypeDeclElem:
            if (options().inlineConstructors && !Modifiers.isAbstract(td.modifiers)) {
                // only process inlined versions of methods
                for (int i = 0; i < td.elems.size(); i++) {
                    TypeDeclElem tde = td.elems.elementAt(i);
                    if (!InlineConstructor.isConstructorInlinable(tde) ||
                        InlineConstructor.isConstructorInlinedMethod((MethodDecl) tde))
                    processTypeDeclElem(tde, sig, initState);
                }
            } else {
                for (int i = 0; i < td.elems.size(); i++) 
                    processTypeDeclElem(td.elems.elementAt(i), sig, initState);
            }
        }

        // ==== all done; clean up ====
        if (prover!=null)
            prover.sendCommand("(BG_POP)");
        
        return false;
    }


    /**
     * Run stages 3+..6 as requested on a TypeDeclElem.
     *
     * requires te is not from a binary file, sig is the
     * TypeSig for te's parent, and initState != null.
     */
    private void processTypeDeclElem(TypeDeclElem te, TypeSig sig,
                     InitialState initState) {
        // Only handle methods and constructors here:
        if (!(te instanceof RoutineDecl))
            return;
        RoutineDecl r = (RoutineDecl)te;


        long startTime = java.lang.System.currentTimeMillis();
        if (!options().quiet) {
            String name = TypeCheck.inst.getRoutineName(r) +
                TypeCheck.inst.getSignature(r);
            System.out.println("\n" + sig.toString() + ": " +
                   name + " ...");
        }

        // Do the actual work, handling not implemented exceptions:
        String status = "error";
        try {
            status = processRoutineDecl(r, sig, initState);
        } catch (javafe.util.NotImplementedException e) {
	    // continue - problem already reported
	    status = "not-implemented";
        } catch (FatalError e) {
	    // continue;
	}
    
        if (!options().quiet)
                System.out.println("    [" + timeUsed(startTime) + "]  "
                               + status);

        /*************************
             System.out.println("Lines " +
                 (Location.toLineNumber(r.getEndLoc())
                     -Location.toLineNumber(r.getStartLoc()))
                     +" time "+timeUsed(startTime));
         *******************/


    }

    /**
     * Run stages 3+..6 as requested on a RoutineDeclElem; returns a
     * short (~ 1 word) status message.
     *
     * requires - r is not from a binary file, sig is the TypeSig
     * for r's parent, and initState != null.
     */
    //@ ensures \result != null;
    private String processRoutineDecl(/*@ non_null */ RoutineDecl r,
                      /*@ non_null */ TypeSig sig,
                      /*@ non_null */ InitialState initState) {

        if (r.body == null) return "passed immediately";
	if (r.parent.specOnly) return "passed immediately";
        if ( Location.toLineNumber(r.getEndLoc()) < options().startLine )
                return "skipped";
        String simpleName = TypeCheck.inst.getRoutineName(r).intern();
        String fullName = sig.toString() + "." + simpleName +
            TypeCheck.inst.getSignature(r);
        fullName = removeSpaces(fullName).intern();
        if (options().routinesToSkip != null &&
                (options().routinesToSkip.contains(simpleName) ||
                options().routinesToSkip.contains(fullName))) {
            return "skipped";
	}
        if (options().routinesToCheck != null &&
                !options().routinesToCheck.contains(simpleName) &&
                !options().routinesToCheck.contains(fullName)) {
            return "skipped";
        }

        // ==== Stage 3 continues here ====
        /*
         * Translate body into a GC:
         */
        long startTime = java.lang.System.currentTimeMillis();
        long routineStartTime = startTime;

        // don't check the body if we're checking some other inlining depth
        Translate.globallyTurnOffChecks(gctranslator.inlineCheckDepth > 0);

        LabelInfoToString.resetToMark();
        GuardedCmd gc = computeBody(r, initState);
        /*@ uninitialized */ /*@ readable_if stats */ int origgcSize = 0;
        if (options().stats) {
                origgcSize = Util.size(gc);
        }

        String gcTime = timeUsed(startTime);
        startTime = java.lang.System.currentTimeMillis();
    
        UniqName.resetUnique();
        if (gc==null)
            return "passed immediately";
        if (options().pgc) {
            System.out.println("\n**** Guarded Command:");
            ((EscPrettyPrint)PrettyPrint.inst).print(System.out, 0, gc);
            System.out.println("");
        }
        Set directTargets = Targets.direct(gc);
        GCSanity.check(gc);

    
        // ==== Start stage 4 ====
        if (stages<4)
            return "ok";

        // Convert GC to DSA:

        String dsaTime = "";
        if (options().dsa) { // always true
            /*
             * From experiements from POPL01 (Cormac)
             gc = passify ? Passify.compute(gc) : DSA.dsa(gc);
             */
            gc = DSA.dsa(gc);
            dsaTime = timeUsed(startTime);
            startTime = java.lang.System.currentTimeMillis();
    
            if (options().pdsa) {
                System.out.println("\n**** Dynamic Single Assignment:");
                ((EscPrettyPrint)PrettyPrint.inst).print(System.out, 0, gc);
                System.out.println("");
            }
        }
    
        // ==== Start stage 5 ====
        if (stages<5)
            return "ok";

        // Generate the VC for GC:
        Expr vcBody;
        /*
         * From experiements from POPL01 (Cormac)
         if(wpnxw != 0 ) {
         vcBody = WpName.compute( gc, wpnxw );
         } else 
         */
        if (options().spvc) {
            /*  
             * From experiements from POPL01 (Cormac)
                 vcBody = wpp ? Wpp.compute(gc, GC.truelit, GC.truelit) : 
                 SPVC.compute(gc);
             */ 
            vcBody = SPVC.compute(gc);
        } else {
            vcBody = Ejp.compute(gc, GC.truelit, GC.truelit);
        }
        Expr vc = GC.implies(initState.getInitialState(), vcBody);
            // Attach a label for use in the logfile generated (if any):
        String label = "vc." + sig.toString() + ".";
        if (r instanceof MethodDecl)
            label += ((MethodDecl)r).id;
        else
            label += "<constructor>";
        label += "." + UniqName.locToSuffix(r.getStartLoc());
        vc = LabelExpr.make(r.getStartLoc(), r.getEndLoc(),
                false, Identifier.intern(label), vc);

        // Check for VC too big:
        int usize = Util.size(vc, options().vclimit);
        if (usize == -1) {
            ErrorSet.caution("Unable to check "
                             + TypeCheck.inst.getName(r)
                             + " of type " + TypeSig.getSig(r.parent)
                             + " because its VC is too large");
            return "VC too big";
        }

        if (options().printAssumers) {
            System.out.print("ASSUMERS: ");
            System.out.print(Location.toFileName(r.getStartLoc()));
            System.out.print('|');
            System.out.print(fullName);
            System.out.println(LabelInfoToString.get());
        }

        String ejpTime = timeUsed(startTime);
        startTime = java.lang.System.currentTimeMillis();
        // Translate VC to a string
        Info.out("[converting VC to a string]");
        if (options().pvc || (Info.on && options().traceInfo > 0))
            VcToString.compute(vc, System.out);
        if (options().guardedVC) {
            String fn = UniqName.locToSuffix(r.locId) + ".method." + 
                options().guardedVCFileExt;
            PrintStream o = fileToPrintStream(options().guardedVCDir, fn);
            o.println(options().MethodVCPrefix);
            o.println(r.parent.id + "@" + UniqName.locToSuffix(r.parent.locId));
            VcToString.compute(vc, o);
            o.close();
            return "guarded VC generation finished";
        }

        String vcTime = timeUsed(startTime);
        startTime = java.lang.System.currentTimeMillis();

        // ==== Start stage 6 ====
        if (stages<6)
            return "ok";

        // Check the VC:
        prover.startProve();

        VcToString.compute(vc, prover.subProcessToStream());
        //,,,
        //  FindContributors scope = new FindContributors(sig);
        //  System.out.println("+++");
        //  escjava.backpred.BackPred.genTypeBackPred(scope, System.out);
        //  VcToString.compute(vc, System.out);
        //  System.out.println("+++");
        Enumeration results = prover.streamProve();

        // Process Simplify's output
        String status = "unexpectedly missing Simplify output";
        boolean nextWarningNeedsPrecedingLine = true;
        while (results.hasMoreElements()) {
            SimplifyOutput so = (SimplifyOutput)results.nextElement();
            switch (so.getKind()) {
                case SimplifyOutput.VALID:
                    status = "passed";
                    break;
                case SimplifyOutput.INVALID:
                    status = "failed";
                    break;
                case SimplifyOutput.UNKNOWN:
                    status = "timed out";
                    break;
                case SimplifyOutput.COMMENT: {
                    SimplifyComment sc = (SimplifyComment)so;
                    System.out.println("SIMPLIFY: " + sc.getMsg());
                    break;
                }
                case SimplifyOutput.COUNTEREXAMPLE: {
                    if (nextWarningNeedsPrecedingLine) {
                        escjava.translate.ErrorMsg.printSeparatorLine(System.out);
                        nextWarningNeedsPrecedingLine = false;
                    }
                    SimplifyResult sr = (SimplifyResult)so;
                    escjava.translate.ErrorMsg.print(TypeCheck.inst.getName(r),
                                                     sr.getLabels(), sr.getContext(),
                                                     r, directTargets, System.out);
                    break;
                }
                case SimplifyOutput.EXCEEDED_PROVER_KILL_TIME: {
                    SimplifyResult sr = (SimplifyResult)so;
                    ErrorSet.caution("Unable to check " +
                                     TypeCheck.inst.getName(r) +
                                     " of type " + TypeSig.getSig(r.parent) +
                                     " completely because too much time required");
                    if (Info.on && sr.getLabels() != null) {
                        Info.out("Current labels: " + sr.getLabels());
                    }
                    nextWarningNeedsPrecedingLine = true;
                    break;
                }
                case SimplifyOutput.EXCEEDED_PROVER_KILL_ITER: {
                    SimplifyResult sr = (SimplifyResult)so;
                    ErrorSet.caution("Unable to check " +
                                     TypeCheck.inst.getName(r) +
                                     " of type " + TypeSig.getSig(r.parent) +
                                     " completely because" +
                                     " too many iterations required");
                    if (Info.on && sr.getLabels() != null) {
                        Info.out("Current labels: " + sr.getLabels());
                    }
                    nextWarningNeedsPrecedingLine = true;
                    break;
                }
                case SimplifyOutput.REACHED_CC_LIMIT:
                    ErrorSet.caution("Not checking " +
                                     TypeCheck.inst.getName(r) +
                                     " of type " + TypeSig.getSig(r.parent) +
                                     " completely because" +
                                     " warning limit (PROVER_CC_LIMIT) reached");
                    break;
                case SimplifyOutput.EXCEEDED_PROVER_SUBGOAL_KILL_TIME: {
                    SimplifyResult sr = (SimplifyResult)so;
                    ErrorSet.caution("Unable to check subgoal of " +
                                     TypeCheck.inst.getName(r) +
                                     " of type " + TypeSig.getSig(r.parent) +
                                     " completely because too much time required");
                    if (Info.on && sr.getLabels() != null) {
                        Info.out("Current labels: " + sr.getLabels());
                    }
                    nextWarningNeedsPrecedingLine = true;
                    break;
                }
                case SimplifyOutput.EXCEEDED_PROVER_SUBGOAL_KILL_ITER: {
                    SimplifyResult sr = (SimplifyResult)so;
                    ErrorSet.caution("Unable to check subgoal of " +
                                     TypeCheck.inst.getName(r) +
                                     " of type " + TypeSig.getSig(r.parent) +
                                     " completely because" +
                                     " too many iterations required");
                    if (Info.on && sr.getLabels() != null) {
                        Info.out("Current labels: " + sr.getLabels());
                    }
                    nextWarningNeedsPrecedingLine = true;
                    break;
                }
                case SimplifyOutput.WARNING_TRIGGERLESS_QUANT: {
                    TriggerlessQuantWarning tqw = (TriggerlessQuantWarning)so;
                    int loc = tqw.getLocation();
                    String msg = "Unable to use quantification because " +
                        "no trigger found: " + tqw.e1;
                    if (loc != Location.NULL) {
                        ErrorSet.caution(loc, msg);
                    } else {
                        ErrorSet.caution(msg);
                    }
                    if (Info.on && tqw.getLabels() != null) {
                        Info.out("Current labels: " + tqw.getLabels());
                    }
                    break;
                }
                default:
                    Assert.fail("unexpected type of Simplify output");
                    break;
            }
        }

        String proofTime = timeUsed(startTime);
        if (options().stats) {
            System.out.println("    [Time: "+timeUsed(routineStartTime)
                               +" GC: "+gcTime
                               +" DSA: "+dsaTime
                               +" Ejp: "+ejpTime
                               +" VC: "+vcTime
                               +" Proof(s): "+proofTime
                               +"]");
            System.out.println("    [Size: "
                               +" src: "+Util.size(r)
                               +" GC: "+origgcSize
                               +" DSA: "+Util.size(gc)
                               +" VC: "+Util.size(vc)
                               +"]");
        }
        return status;
    }

    /**
     * This method computes the guarded command (including assuming
     * the precondition, the translated body, the checked
     * postcondition, and the modifies constraints) for the method or
     * constructor <code>r</code> in scope <code>scope</code>.
     *
     * @return <code>null</code> if <code>r</code> doesn't have a body.
     */

    private GuardedCmd computeBody(RoutineDecl r, InitialState initState) {
        if (r.getTag() == TagConstants.METHODDECL &&
            ((MethodDecl)r).body == null) {
            // no body
            return null;
        }

        // don't check the routine if it's a helper
        if (Helper.isHelper(r)) {
            return null;
        }

        FindContributors scope = new FindContributors(r);
	TrAnExpr.initForRoutine();

        /*
         * Compute an upper bound for synTargs if -O7 given.
         *
         * For now, do this via the kludge of calling trBody...  !!!!
         */
        Set predictedSynTargs = null;
        if (!options().useAllInvPreBody) {
            long T = java.lang.System.currentTimeMillis();
            /*
             * Compute translation assuming synTargs is empty:
             * (gives same set of targets faster than using null)
             */
            GuardedCmd tmpBody = gctranslator.trBody(r, scope,
                                                     initState.getPreMap(),
                                                     /*predictedSynTargs*/new Set(),
                                                     null,
                                                     /* issueCautions */ false);
            if (options().noDirectTargetsOpt)
                predictedSynTargs = Targets.normal(tmpBody);
            else
                predictedSynTargs = Targets.direct(tmpBody);
            if (options().stats)
                System.out.println("      [prediction time: " + timeUsed(T) + "]");
        }



        /*
         * Translate the body:
         */
	    /* Note: initState.preMap is the same for all declarations.
		    This may be overkill (FIXME).
		    It might be better to use information from scope directly
		    since it is generated from the routine decl.
		    However, I don't know for sure what would go missing.  DRCok
	    */

        GuardedCmd body = gctranslator.trBody(r, scope,
                                              initState.getPreMap(),
                                              predictedSynTargs, null,
                                              /* issueCautions */ true);

        Set fullSynTargs = Targets.normal(body);
        Set synTargs;
        if (options().noDirectTargetsOpt)
            synTargs = fullSynTargs;
        else
            synTargs = Targets.direct(body);


        /*
         * Verify predictedSynTargs if present that
         * synTargs is a subset of predictedSynTargs.
         */
        if (predictedSynTargs!=null) {
            Enumeration e = synTargs.elements();
            while (e.hasMoreElements()) {
                GenericVarDecl target = (GenericVarDecl)(e.nextElement());
                Assert.notFalse(predictedSynTargs.contains(target));
            }
        }


        Spec spec = GetSpec.getSpecForBody(r, scope, synTargs,
                                           initState.getPreMap());
	gctranslator.addMoreLocations(spec.postconditionLocations);

        // if the current RoutineDecl corresponds to one of our
        // constructor-inlined methods, then zero out its postconditions
        if (r instanceof MethodDecl &&
            InlineConstructor.isConstructorInlinedMethod((MethodDecl) r))
                spec.post = ConditionVec.make();

        GuardedCmd fullCmd = 
            GetSpec.surroundBodyBySpec(body, spec, scope, fullSynTargs,
                                       initState.getPreMap(),
                                       r.getEndLoc());

        if (Main.options().loopTranslation == Options.LOOP_SAFE 
                                 && Main.options().predAbstract) {
            long T = java.lang.System.currentTimeMillis();
            Traverse.compute(fullCmd, initState, gctranslator);
            if (options().stats) {
                System.out.println("      [predicate abstraction time: " + 
                                   timeUsed(T) + "]");
            }
        }
        Translate.addTraceLabelSequenceNumbers(fullCmd);

        return fullCmd;

    }


    // Misc. Utility routines

    private static String removeSpaces(/*@ non_null */ String s) {
        while (true) {
            int k = s.indexOf(' ');
            if (k == -1) {
                return s;
            }
            s = s.substring(0, k) + s.substring(k+1);
        }
    }
}
