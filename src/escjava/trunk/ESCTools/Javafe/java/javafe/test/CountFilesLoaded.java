/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.test;


import javafe.Tool;
import javafe.SrcTool;
import javafe.ast.TypeDecl;
import javafe.tc.TypeCheck;
import javafe.tc.OutsideEnv;


/**
 **/

public class CountFilesLoaded extends SrcTool {

    /***************************************************
     *                                                 *
     * Generating a usage message:		       *
     *                                                 *
     ***************************************************/

    /**
     ** Return the name of this tool.  E.g., "ls" or "cp".<p>
     **
     ** Used in usage and error messages.<p>
     **/
    public String name() { return "CountFilesLoaded"; }

    /**
     ** Print option information to <code>System.err</code>.  Each
     ** printed line should be preceeded by two blank spaces. <p>
     **
     ** Each overriding method should first call
     ** <code>super.showOptions()</code>.<p>
     **/
    public void showOptions() {
        super.showOptions();

	System.err.println("  -eager");
    }


    /***************************************************
     *                                                 *
     * Generic option processing:		       *
     *                                                 *
     ***************************************************/

    /**
     ** Process next tool option. <p>
     **
     ** See <code>Tool.processOption</code> for the complete
     ** specification of this routine.<p>
     **/
    public int processOption(String option, String[] args, int offset) {
	if (option.equals("-eager")) {
	    OutsideEnv.eagerRead = true;
	    return offset;
	}

	// Pass on unrecognized options:
	return super.processOption(option, args, offset);
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
     ** <b>Note</b>: this code needs to be copied verbatim to each
     ** subclass of <code>Tool</code> except with the name of the actual
     ** subclass inserted after the new operator and the comment
     ** characters (//) removed.<p>
     **
     ** (This needs to be done because static methods cannot be
     ** inherited.)<p>
     **/
    //@ requires \nonnullelements(args)
    public static void main(String[] args) {
	Tool t = new CountFilesLoaded();
	t.run(args);
    }


    /***************************************************
     *                                                 *
     * SrcTool-instance specific processing:	       *
     *                                                 *
     ***************************************************/

    /**
     ** Hook for any work needed after <code>handleCU</code> has been called
     ** on each <code>CompilationUnit</code> to process them.
     **/
    public void postprocess() {
	System.out.println("Files parsed/loaded = " + OutsideEnv.filesRead());
    }


    /**
     ** This method is called on the TypeDecl of each
     ** outside type that SrcTool is to process. <p>
     **/
    public void handleTD(TypeDecl td) {
	if (!td.specOnly)
	    TypeCheck.inst.checkTypeDecl(td);
    }
}
