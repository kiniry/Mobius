/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.reader;


import java.io.IOException;

import javafe.ast.CompilationUnit;
import javafe.ast.PrettyPrint;			// Debugging methods only

import javafe.genericfile.*;

import javafe.parser.Lex;
import javafe.parser.Parse;
import javafe.parser.PragmaParser;

import javafe.util.FileCorrelatedReader;
import javafe.util.Location;


/**
 ** A SrcReader is a Reader that reads in CompilationUnits from source
 ** files (.java files) using the javafe.parser package.<p>
 **
 ** SrcReaders do not cache the results of their reading.<p>
 **/

public class SrcReader extends Reader {

    /***************************************************
     *                                                 *
     * Creation:				       *
     *                                                 *
     ***************************************************/

    //@ invariant readLex!=null;
    private Lex readLex;

    //@ invariant readParser!=null
    private Parse readParser;

    public SrcReader() {
	this(null);
    }

    public SrcReader(PragmaParser p) {
	readLex = new Lex(p, true);
	readParser = new Parse();
    }


    /***************************************************
     *                                                 *
     * Reading:					       *
     *                                                 *
     ***************************************************/

    /**
     ** Attempt to read and parse a CompilationUnit from *source* target.
     ** Any errors encountered are reported via javafe.util.ErrorSet.
     ** Null is returned iff an error was encountered.<p>
     **
     **
     ** By default, we attempt to read only a spec (e.g., specOnly is set
     ** in the resulting CompilationUnit) to save time.  If avoidSpec is
     ** true, we always return a non-spec.<p>
     **
     **
     ** The result of this function is not cached.<p>
     **
     ** Target must be non-null.<p>
     **/
    public CompilationUnit read(GenericFile target, boolean avoidSpec) {
	javafe.util.Info.out("[parsing "
			     + (avoidSpec ? "" : "spec from ")
			     + target.getHumanName() + "]");
	try {
	    FileCorrelatedReader input = new FileCorrelatedReader(target);
	    readLex.restart(input);
        } catch (IOException e) {
	    javafe.util.ErrorSet.error("I/O error: " + e.getMessage());
	    return null;
	}
	CompilationUnit result =
	    readParser.parseCompilationUnit(readLex, !avoidSpec);
	readLex.close();
	return result;
    }


    /***************************************************
     *                                                 *
     * Test methods:				       *
     *                                                 *
     ***************************************************/

    //@ requires \nonnullelements(args)
    public static void main(String[] args) {
	if (args.length!=1) {
	    System.err.println("SrcReader: <source filename>");
	    System.exit(1);
	}

	GenericFile target = new NormalGenericFile(args[0]);
	SrcReader reader = new SrcReader();

	CompilationUnit cu = reader.read(target, true);
	if (cu!=null)
	    PrettyPrint.inst.print( System.out, cu );
    }
}
