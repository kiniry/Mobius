/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.reader;

import javafe.ast.CompilationUnit;
import javafe.ast.LexicalPragmaVec;
import javafe.ast.Modifiers;
import javafe.ast.Identifier;
import javafe.ast.Name;
import javafe.ast.*;
import javafe.ast.TypeDecl;
import javafe.ast.TypeDeclVec;
import javafe.tc.TypeSig;
import javafe.ast.PrettyPrint;			// Debugging methods only
import javafe.ast.StandardPrettyPrint;		// Debugging methods only
import javafe.ast.DelegatingPrettyPrint;	// Debugging methods only
import escjava.ast.EscPrettyPrint;		// Debugging methods only
import javafe.util.Location;
import escjava.ast.RefinePragma;
import escjava.ast.*;
import escjava.ast.TagConstants; // Resolves ambiguity
import escjava.RefinementSequence;

import escjava.AnnotationHandler;
import javafe.genericfile.*;
import javafe.parser.PragmaParser;
import javafe.filespace.Tree;
import javafe.filespace.Query;

import javafe.util.Assert;
import javafe.util.ErrorSet;

import javafe.reader.*;
import javafe.tc.OutsideEnv;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.Iterator;
import java.io.File;
import java.io.FilenameFilter;

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
    protected EscTypeReader(Query engine, Query srcEngine, 
			CachedReader srcReader,
			CachedReader binReader) {
	super(engine, srcEngine, srcReader, binReader);
    }


    // Public creation

    /**
     * Create a <code>EscTypeReader</code> from a query engine, a
     * source reader, and a binary reader.  All arguments must be
     * non-null.
     */
    //@ requires engine != null && srcReader != null && binReader != null;
    //@ ensures \result != null;
    public static StandardTypeReader make(Query engine, 
					Query srcEngine, CachedReader srcReader,
					  CachedReader binReader) {
	return new EscTypeReader(engine, srcEngine, srcReader, binReader);
    }

    /**
     * Create a <code>EscTypeReader</code> from a non-null query
     * engine and a pragma parser.  The pragma parser may be null.
     */
    //@ requires Q != null;
    //@ ensures \result != null;
    public static StandardTypeReader make(Query Q, Query sourceQ,
			PragmaParser pragmaP, AnnotationHandler ah) {
	Assert.precondition(Q != null);

	return make(Q, sourceQ, new RefinementCachedReader(
					new SrcReader(pragmaP)), 
				new CachedReader(new BinReader()));
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
    public static StandardTypeReader make(String path, String srcPath,
			    PragmaParser pragmaP, AnnotationHandler ah) {
	if (path==null)
	    path = javafe.filespace.ClassPath.current();
	Query q = StandardTypeReader.queryFromClasspath(path);

	Query srcq = srcPath == null ? q : 
			StandardTypeReader.queryFromClasspath(srcPath);
	
	return make(q, srcq, pragmaP, ah);
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
	return make((String)null, (String)null, pragmaP);
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
	for (int i=0; i<activeSuffixes.length; ++i) {
	    if (javaSrcFileSpace.findFile(P, T, activeSuffixes[i]) != null) {
		return true;
	    }
	}
	return false;
    }

    public GenericFile findFirst(String[] P, String T) {
	return javaSrcFileSpace.findFile(P,T,activeSuffixes);
    }

    public GenericFile findSrcFile(String[] P, String filename) {
	return javaSrcFileSpace.findFile(P,filename);
    }

    public GenericFile findBinFile(String[] P, String filename) {
	return javaFileSpace.findFile(P,filename);
    }

    public GenericFile findType(String[] P, String T) {
        GenericFile gf = javaSrcFileSpace.findFile(P,T,activeSuffixes);
        if (gf == null) gf = javaFileSpace.findFile(P, T, "class");
        return gf;
    }



    public FilenameFilter filter() {
	return new FilenameFilter() {
	    public boolean accept(File f, String n) {
		int p = n.indexOf('.');
		if (p == -1) return false;
		n = n.substring(p+1);
		for (int i=0; i<activeSuffixes.length; ++i) {
		    if (n.equals(activeSuffixes[i])) { 
			return true;
		    }
		}
		return false;
	    }
	};
    }

    String[] activeSuffixes = { "refines-java", "refines-spec", "refines-jml",
			  "java", "spec", "jml" };

    String[] nonJavaSuffixes = { "refines-java", "refines-spec", "refines-jml",
			  "spec", "jml",
			  "java-refined", "spec-refined", "jml-refined" };

    // Reading

    public CompilationUnit read(GenericFile f, boolean avoidSpec) {
	return super.read(f,avoidSpec);
    }

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
	for (int i=0; i<activeSuffixes.length; ++i) {
	    GenericFile spec = javaSrcFileSpace.findFile(P, T, activeSuffixes[i]);
	    if (spec != null) {
	        return read(spec, false);
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
