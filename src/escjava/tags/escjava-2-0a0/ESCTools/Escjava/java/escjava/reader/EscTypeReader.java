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
    protected EscTypeReader(Query engine, Query srcEngine, Reader srcReader,
			      Reader binReader) {
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
					Query srcEngine, Reader srcReader,
					  Reader binReader) {
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

	return make(Q, sourceQ, new EscSrcReader(pragmaP,ah), new BinReader());
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
	    javafe.util.Info.out("Reading " + target);
	    boolean refining = this.refining;
	    this.refining = false;
	    CompilationUnit result = super.read(target,avoidSpec);
	    if (refining || result == null) return result;
	    result = readRefinements(result);
	    if (result != null) annotationHandler.handlePragmas(result);
	    return result;
	}

	public CompilationUnit readRefinements(CompilationUnit cu) {
     
	    Name pkgName = cu.pkgName;
	    TypeDeclVec types = cu.elems;
	    Identifier type = null;
	    for (int i=0; i<types.size(); ++i) {
		TypeDecl td = types.elementAt(i);
		if (Modifiers.isPublic(td.modifiers)) {
		    type = td.id;
		    break;
		}
	    }
	    if (type == null) {
		// No public type declaration
		// Do no refinement processing
		return cu;
	    }
	    String pkg = pkgName == null ? "" : pkgName.printName();
	    //System.out.println("CU " + pkg + " " + type);
	    String[] pkgStrings = pkgName == null ? new String[0] : 
					pkgName.toStrings();

	    ArrayList refinements = getRefinementSequence(pkgStrings, type, cu);
	    if (refinements == null) return null;
	    if (refinements.size() == 0) return cu;


		// FIXME - Probably does not work for nested classes.
	    GenericFile javafile = ((EscTypeReader)OutsideEnv.reader).findSrcFile(pkgStrings,type.toString()+".java");
	    CompilationUnit javacu = null;
	    if (javafile != null) {
		if (javafile.getCanonicalID().equals(cu.sourceFile().getCanonicalID())) javacu = cu;
		else for (int i=0; javacu == null && i<refinements.size(); ++i) {
		    CompilationUnit rcu = (CompilationUnit)refinements.get(i);
		    if (rcu.sourceFile().getCanonicalID().equals(javafile))
			    javacu = rcu;
		}
	    }
	    //System.out.println("HAVE " + cu.sourceFile().getHumanName());
	    if (javacu == null) {
		if (javafile != null) {
		    //System.out.println("READING SOURCE " + javafile.getHumanName());
		    ErrorSet.caution("The file " + javafile + " is not in the refinement sequence that begins with " + cu.sourceFile() + "; it is used to generate a class signature, but no refinements within it are used.");
		    javacu = super.read(javafile, false);
		} else {
	    	    javafile = ((EscTypeReader)OutsideEnv.reader).findBinFile(pkgStrings,type.toString()+".class");
		    //System.out.println("READING BINARY " + javafile.getHumanName());
		    if (javafile != null) javacu = ((EscTypeReader)OutsideEnv.reader).binaryReader.read(javafile, false); //read the binary??? FIXME
		}
	    }
// FIXME - really want a routine that reads binary if up to date otherwise 
// source, simply to get signature.  Read java with bodies if it is one of the
// files to be checked.  The above should be able to be greatly improved!!!!
     
	    CompilationUnit newcu = new RefinementSequence(refinements,javacu,annotationHandler);
	    //newcu = consolidateRefinements(refinements,javacu);
	    return newcu;
	}
     

        boolean refining = false;

	// result is a list of CompilationUnits
	ArrayList getRefinementSequence(String[] pkgStrings, Identifier type, 
				CompilationUnit cu) {
	    ArrayList refinements = new ArrayList();
	    GenericFile gf = cu.sourceFile();
	    String gfid = gf.getCanonicalID();
	    GenericFile mrcufile =
		((EscTypeReader)OutsideEnv.reader).findFirst(
			pkgStrings,type.toString());
	    javafe.util.Info.out( mrcufile==null ? "No MRCU found" :
			"Found MRCU " + mrcufile);
	    // If no MRCU is found in the sourcepath, then we presume that
	    // the file on the command line is that.
	    GenericFile gfile = (mrcufile == null) ? gf : mrcufile ;
	    EscTypeReader tr = (EscTypeReader)OutsideEnv.reader;
	    CompilationUnit ccu;
	    boolean foundCommandLineFileInRS = false;
	    while(gfile != null) {
		if (gfile.getCanonicalID().equals(gfid)) {
		    // Avoid parsing a file twice
		    ccu = cu;
		    foundCommandLineFileInRS = true;
                } else {
		    refining = true;
		    ccu = tr.read(gfile,false);
		    refining = false;
		}
		refinements.add(ccu);
		gfile = findRefined(pkgStrings,ccu);
		if (gfile != null) {
		  if (!gfile.getLocalName().startsWith(type.toString() + ".")){
			ErrorSet.caution("The refinement file " + gfile +
			    " in the sequence beginning with " + mrcufile +
			    " has a prefix that does not match the type name "
			    + type);
		  }
		  for (int i=0; i<refinements.size(); ++i) {
		    if ( ((CompilationUnit)refinements.get(i)).sourceFile().
			getCanonicalID().equals( gfile.getCanonicalID() )) {
			ErrorSet.error(gfile.getHumanName() + 
				" is circularly referenced in a refinement sequence");
			gfile = null;
			break;
		    }
		  }
		}
	    }
	    if (!foundCommandLineFileInRS) {
		String pkg = cu.pkgName == null ? "" : 
				cu.pkgName.printName() + ".";
		if (refinements.size() == 0) {
		    // If no refinement sequence was found, we simply use the
		    // file on the command line, even if it is not on the
		    // classpath.
		    refinements.add(cu);
		} else {
		    String err = "The command-line argument " 
			+ cu.sourceFile().getHumanName() 
			+ " was not in the refinement sequence for type " 
			+ pkg + type.toString() + ":";
		    for (int k = 0; k<refinements.size(); ++k) {
			err += " " + ((CompilationUnit)refinements.get(k)).
					sourceFile().getHumanName();
		    }
		    ErrorSet.error(err);
		    return null;
		}
	    }
	    return refinements;
	}

	public static GenericFile findRefined(String[] pkgStrings, CompilationUnit cu) {
	    LexicalPragmaVec v = cu.lexicalPragmas;
	    for (int i=0; i<v.size(); ++i) {
		if (v.elementAt(i) instanceof RefinePragma) {
		    RefinePragma rp = (RefinePragma)v.elementAt(i);
		    String filename = rp.filename;
			// FIXME - what if we are refining a class file ???
		    GenericFile gf = ((EscTypeReader)OutsideEnv.reader).findSrcFile(pkgStrings,filename);
		    if (gf == null) ErrorSet.error(rp.loc,
			"Could not find file referenced in refine annotation: " + filename);
		    return gf;
     
    // FIXME - hsould be able to have refined files that are not in regular files as well
		}
	    }
	    return null;
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
	for (int i=0; i<nonJavaSuffixes.length; ++i) {
	    if (javaSrcFileSpace.findFile(P, T, nonJavaSuffixes[i]) != null) {
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

    // Finds source files
    public ArrayList findFiles(String[] P) {
	Enumeration e = javaSrcFileSpace.findFiles(P);
	if (e == null) return null;
	ArrayList a = new ArrayList();
	while (e.hasMoreElements()) {
	    Tree t = (Tree)e.nextElement();
	    String s = t.getLabel();
	    int p = s.lastIndexOf('.');
	    if (p == -1) continue;
	    String suffix = s.substring(p+1);
	    for (int i=0; i<activeSuffixes.length; ++i) {
		if (suffix.equals(activeSuffixes[i])) { 
		    a.add(t.data); 
		    break; 
		}
	    }
        }
	return a;
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
	for (int i=0; i<nonJavaSuffixes.length; ++i) {
	    GenericFile spec = javaSrcFileSpace.findFile(P, T, nonJavaSuffixes[i]);
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
