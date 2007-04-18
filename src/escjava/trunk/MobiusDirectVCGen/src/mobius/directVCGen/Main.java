package mobius.directVCGen;

import javafe.ast.DelegatingPrettyPrint;
import javafe.ast.StandardPrettyPrint;
import javafe.ast.TypeDecl;
import javafe.tc.OutsideEnv;
import javafe.tc.TypeSig;
import javafe.util.ErrorSet;
import javafe.util.Location;
import mobius.directVCGen.vcgen.DirectVCGen;
import escjava.ast.EscPrettyPrint;
import escjava.tc.TypeCheck;
import escjava.translate.NoWarn;

public class Main extends escjava.Main {
	
	/**
	 * The main entry point.
	 * @param args ESC/Java styles of args - most of them will be
	 * ignored anyway -
	 */
	public static void main(/*@ non_null @*/ String[] args) {
		int exitcode = compile(args);
		if (exitcode != 0) 
			System.exit(exitcode);
	}
	
	
	public static int compile(String[] args) {
	    try {
	    	Main t = new Main();
	    	//instance = t;
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
	
	
	/*
	 * Remove the check for the use of a legitimate VM
	 * (non-Javadoc)
	 * @see escjava.Main#preload()
	 */
	public void preload() {
	    	OutsideEnv.setListener(this);
	}
	
	/**
	 * This method is called by SrcTool on the TypeDecl of each
	 * outside type that SrcTool is to process.
	 *
	 * <p> In addition, it calls itself recursively to handle types
	 * nested within outside types.
	 */
	//@ also
	//@ requires td != null;
	public void handleTD(TypeDecl td) {
	    long startTime = currentTime();
	    javafe.tc.TypeSig sig = TypeCheck.inst.getSig(td);
	
	    if (!options().quiet)
	        System.out.println("\n" + sig.toString() + " ...");
	
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
	 * Run the stage1 (just type checking and pretty print)
	 * and then runs the VCGen
	 */
	//@ requires td != null;
	//@ requires (* td is not from a binary file. *);
	@SuppressWarnings("unchecked")
	public boolean processTD(TypeDecl td) {
		int errorCount = ErrorSet.errors;
		
		long startTime = currentTime();
		TypeSig sig = TypeCheck.inst.getSig(td);
		sig.typecheck();
		processTD_stage1(td, sig, errorCount);
		System.out.println("[" + timeUsed(startTime) + "]\n");
		
		long midTime = currentTime();
		sig.getCompilationUnit().accept(new DirectVCGen());
	    System.out.println("[" + timeUsed(midTime) + "]\n");

	    return false;
	    
	}
	
	/**
	 * Stage 1: Do Java type checking then print Java types if we've been
	 * asked to.
	 */
	public boolean processTD_stage1(TypeDecl td, TypeSig sig, int errorCount) {
	
	    NoWarn.typecheckRegisteredNowarns();
	
		// Create a pretty-printer that shows types
		DelegatingPrettyPrint p = new javafe.tc.TypePrint();
		p.setDel(new EscPrettyPrint(p, new StandardPrettyPrint(p)));
		System.out.println("\n**** Source code with types:");
		p.print(System.out, 0, td);
	
	    // Turn off extended static checking and abort if any errors
	    // occured while type checking *this* TypeDecl:
	    if (errorCount < ErrorSet.errors) {
			if (stages>1) {
			    stages = 1;
			    ErrorSet.caution("Turning off extended static checking " + 
	                                     "due to type error(s)");
			}
			return false;
	    }   
		return true;
	}
	

}
