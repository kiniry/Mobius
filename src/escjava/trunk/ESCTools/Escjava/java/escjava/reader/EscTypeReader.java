/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.reader;

import javafe.ast.CompilationUnit;
import javafe.ast.TypeDecl;
import javafe.ast.PrettyPrint;			// Debugging methods only
import javafe.ast.StandardPrettyPrint;		// Debugging methods only
import javafe.ast.DelegatingPrettyPrint;	// Debugging methods only
import escjava.ast.EscPrettyPrint;		// Debugging methods only

import escjava.AnnotationHandler;
import javafe.genericfile.*;
import javafe.parser.PragmaParser;

import javafe.filespace.Query;

import javafe.util.Assert;
import javafe.util.ErrorSet;

import javafe.reader.*;

/**
 * An <code>EscTypeReader</code> is a <code>StandardTypeReader</code>
 * extended to understand ".spec" files.
 */

public class EscTypeReader extends StandardTypeReader
{
    // Private creation

    /**
     * Create an <code>ESCTypeReader</code> from a query engine, a
     * source reader, and a binary reader.  All arguments must be
     * non-null.
     */
    //@ requires engine != null && srcReader != null && binReader != null;
    protected EscTypeReader(Query engine, Reader srcReader,
			      Reader binReader) {
	super(engine, srcReader, binReader);
    }


    // Public creation

    /**
     * Create a <code>EscTypeReader</code> from a query engine, a
     * source reader, and a binary reader.  All arguments must be
     * non-null.
     */
    //@ requires engine != null && srcReader != null && binReader != null;
    //@ ensures \result != null;
    public static StandardTypeReader make(Query engine, Reader srcReader,
					  Reader binReader) {
	return new EscTypeReader(engine, srcReader, binReader);
    }

    /**
     * Create a <code>EscTypeReader</code> from a non-null query
     * engine and a pragma parser.  The pragma parser may be null.
     */
    //@ requires Q != null;
    //@ ensures \result != null;
    public static StandardTypeReader make(Query Q,
			PragmaParser pragmaP, AnnotationHandler ah) {
	Assert.precondition(Q != null);

	return make(Q, new EscSrcReader(pragmaP,ah), new BinReader());
    }

    /* We have to make this subclass of SrcReader because: a file that
	is listed on the command line is processed by the sequence of
	code in SrcTool (and subclasses).  This calls OutsideEnv.addSource
	(which calls SrcReader.read) to do the java file parsing, and then 
	proceeds with other processing to do various typechecking.  
	However, types that are referenced in a given file also need to be
	loaded.  These are loaded by a different mechanism
	and only SrcReader.read is called.  Now when import pragmas are
	parsed by the pragmaParser, the compilation unit is not available
	to add the imports into; hence we have to handle the import
	pragmas after the compilation unit is completed.  But SrcReader.read
	does not provide the opportunity to do so.  Hence we have to override
	it here so that we can process the pragmas and get the right
	declarations (imports and model methods) in scope.
    */

    public static class EscSrcReader extends javafe.reader.SrcReader {

	protected AnnotationHandler annotationHandler;

	public EscSrcReader(PragmaParser pragmaP, AnnotationHandler ah) {
		super(pragmaP);
		annotationHandler = ah;
	}

	public CompilationUnit read(GenericFile target, boolean avoidSpec) {
		CompilationUnit result = super.read(target,avoidSpec);
		annotationHandler.handlePragmas(result);
		return result;
	}
    }
		
    /**
     * Create a <code>EscTypeReader</code> using a given Java
     * classpath for our underlying Java file space and a given pragma
     * parser.  If the given path is null, the default Java classpath
     * is used.
     *
     * <p> A fatal error will be reported via <code>ErrorSet</code> if
     * an I/O error occurs while initially scanning the filesystem.
     */
    //@ ensures \result != null;
    public static StandardTypeReader make(String path,
			    PragmaParser pragmaP, AnnotationHandler ah) {
	if (path==null)
	    path = javafe.filespace.ClassPath.current();
	
	return make(StandardTypeReader.queryFromClasspath(path), pragmaP, ah);
    }

    /**
     * Create a <code>EscTypeReader</code> using a the default Java
     * classpath for our underlying Java file space and a given pragma
     * parser.
     *
     * <p> A fatal error will be reported via <code>ErrorSet</code> if
     * an I/O error occurs while initially scanning the filesystem.
     */
    //@ ensures \result != null;
    public static StandardTypeReader make(PragmaParser pragmaP) {
	return make((String)null, pragmaP);
    }

    /**
     * Create a <code>EscTypeReader</code> using the default Java
     * classpath for our underlying Java file space and no pragma
     * parser.
     *
     * <p> A fatal error will be reported via <code>ErrorSet</code> if
     * an I/O error occurs while initially scanning the filesystem.
     */
    //@ ensures \result != null;
    public static StandardTypeReader make() {
	return make((PragmaParser) null);
    }


    // Existance/Accessibility

    /**
     * Return true iff the fully-qualified outside type P.T exists.
     */
    public boolean exists(String[] P, String T) {
	if ( super.exists(P, T)) return true;
	for (int i=0; i<suffixes.length; ++i) {
	    if (javaFileSpace.findFile(P, T, suffixes[i]) != null) {
		return true;
	    }
	}
	return false;
    }

    String[] suffixes = { "refines-java", "refines-spec", "refines-jml",
			  "spec", "jml",
			  "java-refined", "spec-refined", "jml-refined" };

    // Reading

    /**
     * Override {@link StandardTypeReader#read(String[], String, boolean)}
     * method to include ".spec" files.
     */
    public CompilationUnit read(String[] P, String T,
				boolean avoidSpec) {
	// If a source exists and we wish to avoid specs, use it:
	if (avoidSpec) {
	    GenericFile src = locateSource(P, T, true);
	    if (src != null) {
		return super.read(src, true);
	    }
	}

	// If not, use spec file if available:
	for (int i=0; i<suffixes.length; ++i) {
	    GenericFile spec = javaFileSpace.findFile(P, T, suffixes[i]);
	    if (spec != null) {
	        return super.read(spec, false);
	    }
	}

	// Lastly, try source in spec mode then the binary:
	GenericFile source = locateSource(P, T, true);
	if (source != null)
	    return super.read(source, false);
	return super.read(P, T, avoidSpec);	// only a binary exists...
    }

    /**
     * Does a CompilationUnit contain a specOnly TypeDecl?
     */
    //@ requires cu != null;
    boolean containsSpecOnly(CompilationUnit cu) {
	for (int i=0; i<cu.elems.size(); i++) {
	    TypeDecl d = cu.elems.elementAt(i);
	    //@ assume d != null;

	    if (d.specOnly)
		return true;
	}

	return false;
    }


    // Test methods

    //@ requires \nonnullelements(args);
    public static void main(String[] args)
            throws java.io.IOException {
	if (args.length<2 || args.length>3
	    || (args.length==3 && !args[2].equals("avoidSpec"))) {
	    System.err.println("EscTypeReader: <package> <simple name>"
			       + " [avoidSpec]");
	    System.exit(1);
	}

	javafe.util.Info.on = true;

	String[] P = javafe.filespace.StringUtil.parseList(args[0], '.');
	StandardTypeReader R = make(new escjava.parser.EscPragmaParser());

	DelegatingPrettyPrint p = new EscPrettyPrint();
	p.del = new StandardPrettyPrint(p);
	PrettyPrint.inst = p;


	CompilationUnit cu = R.read(P, args[1], args.length==3);
	if (cu==null) {
	    System.out.println("Unable to load that type.");
	    System.exit(1);
	}

	PrettyPrint.inst.print( System.out, cu );
    }
}
