/* Copyright 2000, 2001, Compaq Computer Corporation */

package javafe.reader;

import javafe.ast.CompilationUnit;
import javafe.ast.PrettyPrint;			// Debugging methods only

import javafe.genericfile.*;
import javafe.parser.PragmaParser;

import javafe.filespace.Query;
import javafe.filespace.SlowQuery;
import javafe.filespace.Tree;

import javafe.Options;
import javafe.Tool;

import javafe.util.Assert;
import javafe.util.ErrorSet;

import java.util.Enumeration;
import java.util.ArrayList;
import java.io.File;
import java.io.FilenameFilter;

/**
 * A StandardTypeReader is a {@link TypeReader} that uses {@link
 * javafe.filespace.SlowQuery} to find type files, and user-supplied
 * {@link Reader}s to read source and binary files.
 */

public class StandardTypeReader extends TypeReader
{
    /***************************************************
     *                                                 *
     * Private creation:			       *
     *                                                 *
     **************************************************/

    /**
     * Our (non-null) Query engine for determining the GenericFile's
     * for files that belong to Java Packages.
     */
    //@ invariant javaFileSpace != null;
    public Query javaFileSpace;

    //@ invariant javaSrcFileSpace != null;
    public Query javaSrcFileSpace;

    /**
     * Our (non-null) reader for use in reading in source files.
     */
    //@ invariant sourceReader != null;
    public Reader sourceReader;

    /**
     * Our (non-null) reader for use in reading in binary (.class) files.
     */
    //@ invariant binaryReader != null;
    public Reader binaryReader;


    /**
     * Create a StandardTypeReader from a query engine, a source
     * reader, and a binary reader.  All arguments must be non-null.<p>
     */
    //@ requires engine != null && srcReader != null && binReader != null;
    protected StandardTypeReader(Query engine, Query srcEngine, 
			      CachedReader srcReader,
			      CachedReader binReader) {
	javaFileSpace = engine;
	javaSrcFileSpace = srcEngine;

	// The sourceReader must be cached to meet TypeReader's spec:
	sourceReader = srcReader;

	/*
         * The binaryReader is cached only for efficiency reasons.
	 *  (this prevents duplicate reads of binaries when useSrcPtr is
	 *   used)
	 */
	binaryReader = binReader;
    }

    public void clear() {
	((CachedReader)sourceReader).flushAll();
	((CachedReader)binaryReader).flushAll();
    }

    /***************************************************
     *                                                 *
     * Public creation:				       *
     *                                                 *
     **************************************************/

    /**
     * Create a StandardTypeReader from a query engine, a source
     * reader, and a binary reader.  All arguments must be non-null.<p>
     */
    //@ requires engine != null && srcReader != null && binReader != null;
    //@ ensures \result != null;
    public static StandardTypeReader make(Query engine, Query srcEngine,
					  Reader srcReader,
			                  Reader binReader) {
	return new StandardTypeReader(engine, srcEngine, 
			new CachedReader(srcReader), 
			new CachedReader(binReader));
    }



    /**
     * Create a StandardTypeReader from a non-null query engine and a
     * pragma parser.  The pragma parser may be null.
     */
    //@ requires Q != null;
    //@ ensures \result != null;
    public static StandardTypeReader make(Query Q, Query sourceQ,
						PragmaParser pragmaP) {
	Assert.precondition(Q != null);

	return make(Q, sourceQ, new SrcReader(pragmaP), new BinReader());
    }


    /**
     * Create a Query for use in creating a StandardTypeReader from a
     * Java classpath. <p>
     *
     * A fatal error will be reported via <code>ErrorSet</code> if an
     * I/O error occurs while initially scanning the filesystem.<p>
     */
    //@ requires path != null;
    //@ ensures \result != null;
    public static Query queryFromClasspath(String path) {
	try {
	    return new SlowQuery(path);
	} catch (java.io.IOException e) {
	    ErrorSet.fatal("unable to initialize Java filespace due to"
				+ " I/O error: " + e.getMessage());
	}

	//@ unreachable
	return null;	// make compiler happy
    }


    /**
     * Create a StandardTypeReader using a given Java classpath for our
     * underlying Java file space and a given pragma parser.  If the
     * given path is null, the default Java classpath is used. <p>
     *
     * A fatal error will be reported via <code>ErrorSet</code> if an
     * I/O error occurs while initially scanning the filesystem.<p>
     */
    //@ ensures \result != null;
    public static StandardTypeReader make(String path, String sourcePath,
						PragmaParser pragmaP) {
	if (path==null)
	    path = javafe.filespace.ClassPath.current();
	
	Query q = queryFromClasspath(path);
	Query srcq = sourcePath == null ? q : queryFromClasspath(sourcePath);
	return make(q, srcq, pragmaP);
    }


    /**
     * Create a StandardTypeReader using a the default Java classpath
     * for our underlying Java file space and a given pragma
     * parser. <p>
     *
     * A fatal error will be reported via <code>ErrorSet</code> if an
     * I/O error occurs while initially scanning the filesystem.<p>
     */
    //@ ensures \result != null;
    public static StandardTypeReader make(PragmaParser pragmaP) {
	return make((String)null, (String)null, pragmaP);
    }


    /**
     * Create a StandardTypeReader using the default Java classpath
     * for our underlying Java file space and no pragma parser. <p>
     *
     * A fatal error will be reported via <code>ErrorSet</code> if an
     * I/O error occurs while initially scanning the filesystem.<p>
     */
    //@ ensures \result != null;
    public static StandardTypeReader make() {
	return make((PragmaParser) null);
    }


    /***************************************************
     *                                                 *
     * Existance/Accessibility:			       *
     *                                                 *
     **************************************************/

    /**
     * Return true iff the package P is "accessible".<p>
     *
     * Warning: the definition of accessible is host system dependent
     * and may in fact be defined as always true.<p>
     */
    public boolean accessable(String[] P) {
	return javaSrcFileSpace.accessable(P) || javaFileSpace.accessable(P);
    }


    /**
     * Return true iff the fully-qualified outside type P.T exists.
     */
    public boolean exists(String[] P, String T) {
	return (javaSrcFileSpace.findFile(P, T, "java") != null)
	    || (javaFileSpace.findFile(P, T, "class") != null);
    }

    public GenericFile findType(String[] P, String T) {
	GenericFile gf = javaSrcFileSpace.findFile(P, T, "java");
	if (gf == null) gf = javaFileSpace.findFile(P, T, "class");
	return gf;
    }

    /***************************************************
     *                                                 *
     * Locating types:				       *
     *                                                 *
     **************************************************/

    /**
     * If a binary exists for the exact fully-qualified type P.N (e.g.,
     * no inheritance required), then return a GenericFile representing
     * that file.  Otherwise, return null.<p>
     *
     * WARNING: if N is not a simple name, then a non-null return
     * result does *not* imply that P.N actually exists.  The binary
     * may be left over from a previous compilation.  Only if P.N can
     * be reached from its containing clases, is it considered to
     * exist.<p>
     */
    //@ requires \nonnullelements(P) && \nonnullelements(N)
    public GenericFile locateBinary(String[] P, String[] N) {
	String typename = "";

	for (int i=0; i<N.length; i++) {
	    if (i != 0)
		typename += "$";
	    typename += N[i];
	}

	return javaFileSpace.findFile(P, typename, "class");
    }


    /**
     * If a source exists for the fully-qualified outside type P.T,
     * then return a GenericFile representing that file.  Otherwise,
     * return null.<p>
     *
     * Exception: If P.T's source file is not called T.java, and no
     * T.class file exists for P.T, then null will also be returned.
     * If useSrcPtr is not set, then null will be returned when
     * P.T's source file is not called T.java, regardless of whether or
     * not there is a T.class file for P.T.<p>
     *
     * Note: iff useSrcPtr is set, then P.T's binary may be read in in
     * order to obtain it's source pointer.<p>
     */
    //@ requires \nonnullelements(P) && T != null;
    public GenericFile locateSource(String[] P, String T, boolean useSrcPtr) {
	// First try the .java file with name T.java:
	GenericFile file = javaSrcFileSpace.findFile(P, T, "java");
	if (file != null || !useSrcPtr)
	    return file;

	// Try and fetch the source pointer from T.class:
	String[] N = { T };
	file = locateBinary(P, N);
	if (file==null)
	    return null;
	CompilationUnit binary = binaryReader.read(file, false);
	if (binary==null)
	    return null;
	String srcPtr = "srcptr.java";	// !!!!

	// Try and locate that file if a valid srcPtr is present:
	if (srcPtr==null || !srcPtr.endsWith(".java"))
	    return null;
	return javaSrcFileSpace.findFile(P, srcPtr.substring(0,srcPtr.length()-5),
					"java");
    }


	// Finds source files
    public ArrayList findFiles(String[] P) {
	FilenameFilter ff = filter();
	ArrayList a = new ArrayList();
	Enumeration e = javaSrcFileSpace.findFiles(P);
	while (e.hasMoreElements()) {
	    Tree t = (Tree)e.nextElement();
	    String s = t.getLabel();
	    if (ff.accept(new File(s),s)) { a.add(t.data); }
	}
	return a;
    }

    public FilenameFilter filter() {
	return new FilenameFilter() {
	    public boolean accept(File f, String n) {
		if (!f.isFile()) return false;
		if (n.endsWith(".java")) return true;
		return false;
	    }
	};
    }

    /***************************************************
     *                                                 *
     * Reading:					       *
     *                                                 *
     **************************************************/


    /**
     * Attempt to read and parse a CompilationUnit from *source file*
     * target.  Any errors encountered are reported via
     * javafe.util.ErrorSet.  Null is returned iff an error was
     * encountered.<p>
     *
     *
     * By default, we attempt to read only a spec (e.g., specOnly is set
     * in the resulting CompilationUnit) to save time.  If avoidSpec is
     * true, we return a non-spec, except in the case where we have
     * previously read in the same source file with avoidSpec false.
     * (See notes on caching below.)<p>
     *
     * There are 2 safe ways to ensure source files yield
     * non-spec files: (1) always use avoidSpec, or (2) read all
     * desired non-spec's at the beginning with avoidSpec set.
     * [these instructions apply to both versions of read.]<p>
     *
     *
     * The result of this function is cached.  Note that read(String[],
     * ...) may implicitly call this function, resulting in caching of
     * source files. <p>
     *
     * Only the value of avoidSpec used the first time a given file is
     * read is used (including implicit calls).  This may result in a
     * spec being returned unnecessarily when avoidSpec is true.<p>
     *
     * Target must be non-null.<p>
     */
    public CompilationUnit read(GenericFile target, boolean avoidSpec) {
	return sourceReader.read(target, avoidSpec);
    }


    /**
     * Attempt to read and parse a CompilationUnit from the source for
     * the fully-qualified outside type P.T.  Null is returned if no
     * source can be found for P.T or if an error is encountered.
     * Errors are reported via ErrorSet.<p>
     *
     * If P.T's source is not named T.java and there is no T.class file
     * for P.T., then no source for P.T will be found.<p>
     *
     * (This is a convenience function.)<p>
     */
    //@ requires \nonnullelements(P) && T != null;
    public CompilationUnit readTypeSrc(String[] P, String T,
				       boolean avoidSpec) {
	GenericFile source = locateSource(P, T, true);
	if (source==null)
	    return null;

	return read(source, avoidSpec);
    }


    /**
     * Attempt to read and parse a complete (i.e., no stubs)
     * CompilationUnit from the binaries for the fully-qualified
     * outside type P.T.<p>
     *
     * Null is returned if:<p>
     *
     *    - no T.class file exists,<p>
     *    - the T.class file is known to predate the lastModified time
     *      after, after != 0L, or<p>
     *    - an error occurs.<p>
     *
     * Errors are reported via ErrorSet.  An incomplete set of binaries
     * (one or more inner classes missing or not up-to-date WRT after)
     * is considered an error.<p>
     */
    //@ requires \nonnullelements(P) && T != null;
    public CompilationUnit readTypeBinaries(String[] P, String T,
					    long after) {
	// Check for an up-to-date T.class file:
	String[] N = { T };
	GenericFile bin = locateBinary(P, N);
	if (bin==null || (after != 0L && bin.lastModified() != 0L
				&& bin.lastModified()<after))
	    return null;

	/*
	 * For now, ignore possibility of inner classes and return only
	 * the outside class.  This needs to be fixed later to read in
	 * all the inner classes and stitch them together.  !!!!
	 */
	return binaryReader.read(bin, false);
    }


    /**
     * Attempt to read and parse a CompilationUnit from either the
     * binaries for P.T if they are up to date, or from the source for
     * P.T.  If both a source and an up-to-date series of
     * binaries are available for P.T, preference is given to the
     * source if srcPreferred is set, and to the binaries otherwise.<p>
     *
     * Binaries are considered to exist for P.T iff a T.class file
     * exists in package P.  The lastModified date for these binaries
     * as a whole is considered to be the T.class file's lastModified
     * date.<p>
     *
     * Null is returned if no source or binaries for P.T exist or if an
     * error occurs.  Errors are reported via ErrorSet.  An incomplete
     * series of binaries (one or more inner classes missing or not
     * up-to-date) generates an error when read in.<p>
     *
     * If the resulting CompilationUnit is non-null, then it is always
     * complete, having no stubs.<p>
     */
    public CompilationUnit read(String[] P, String T,
					boolean avoidSpec) {
	int fileOriginOption = Tool.options.fileOrigin;

	// Locate source file, if any:
	GenericFile source = null;
	if (fileOriginOption != Options.NEVER_SOURCE)
		source = locateSource(P, T, true);

	// Last modification date for source if known (0L if not known):
	long after = source==null ? 0L : source.lastModified();

	// If try to avoid spec's, read from source if it exists:
	if (source != null && (avoidSpec 
				|| fileOriginOption == Options.NEVER_BINARY 
				|| fileOriginOption == Options.PREFER_SOURCE))
	    return read(source, avoidSpec);

	// Read from the binaries if they're complete and up-to-date:
	if (fileOriginOption == Options.PREFER_BINARY) after = 0L;
	if (fileOriginOption != Options.NEVER_BINARY) {
	    CompilationUnit bin = readTypeBinaries(P, T, after);
	    if (bin != null) return bin;
	}

	// Finally, fall back on source if it's available:
	if (source != null) return read(source, avoidSpec);

	return null;
    }


    /***************************************************
     *                                                 *
     * Test methods:				       *
     *                                                 *
     **************************************************/

    //@ requires \nonnullelements(args)
    public static void main(String[] args)
			throws java.io.IOException {
	if (args.length != 2) {
	    System.err.println("StandardTypeReader: <package> <simple name>");
	    System.exit(1);
	}

	String[] P = javafe.filespace.StringUtil.parseList(args[0], '.');
	
	StandardTypeReader R = make();

	CompilationUnit cu = R.read(P, args[1], false);
	if (cu==null) {
	    System.out.println("Unable to load that type.");
	    System.exit(1);
	}

	PrettyPrint.inst.print( System.out, cu );
    }
}
