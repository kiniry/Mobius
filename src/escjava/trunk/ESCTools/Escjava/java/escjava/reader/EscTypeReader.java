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

import escjava.AnnotationHandler;
import javafe.genericfile.*;
import javafe.parser.PragmaParser;

import javafe.filespace.Query;

import javafe.util.Assert;
import javafe.util.ErrorSet;

import javafe.reader.*;
import javafe.tc.OutsideEnv;

import java.util.ArrayList;

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

	    GenericFile javafile = ((EscTypeReader)OutsideEnv.reader).findFile(pkgStrings,type.toString()+".java");
	    CompilationUnit javacu = null;
	    if (javafile != null) {
		if (javafile.getCanonicalID().equals(cu.sourceFile().getCanonicalID())) javacu = cu;
		for (int i=0; javacu == null && i<refinements.size(); ++i) {
		    CompilationUnit rcu = (CompilationUnit)refinements.get(i);
		    if (rcu.sourceFile().getCanonicalID().equals(javafile))
			    javacu = rcu;
		}
		if (javacu == null) javacu = OutsideEnv.reader.read(javafile,false);
	    }
     
	    CompilationUnit newcu = consolidateRefinements(refinements,javacu);
	    return newcu;
	}
     
	//@ requires refinements.size() > 0;
	CompilationUnit consolidateRefinements(ArrayList refinements,
		CompilationUnit javacu) {
	    CompilationUnit lastcu = (CompilationUnit)refinements.get(refinements.size()-1);
	    if (javacu != null && refinements.size() == 0) return javacu;
	    if (javacu == null && refinements.size() == 1) return lastcu;
	    CompilationUnit refcu = (javacu != null) ? javacu : lastcu;

	    Name pkgName = refcu.pkgName;
	    LexicalPragmaVec lexicalPragmaVec = LexicalPragmaVec.make();
	    ImportDeclVec imports = ImportDeclVec.make();
	    TypeDeclVec types = TypeDeclVec.make();
	    int loc = refcu.loc;
	    if (refinements.size() > 0)
		loc = ((CompilationUnit)refinements.get(0)).loc;

	    for (int k=refinements.size()-1; k>=0; --k) {
		CompilationUnit cu = (CompilationUnit)refinements.get(k);
		String p = pkgName==null ? "" : pkgName.printName();
		String cp = cu.pkgName==null ? "" : cu.pkgName.printName();
		if (!cp.equals(p)) {
		    ErrorSet.error(cu.loc,"Package name does not match the package name in " + Location.toFile(loc).getHumanName() + ": " +
			cp + " vs. " + p);
		}
		LexicalPragmaVec lexvec = cu.lexicalPragmas;
		for (int i=0; i<lexvec.size(); ++i) {
		    LexicalPragma lexp = lexvec.elementAt(i);
		    if (!(lexp instanceof RefinePragma)) {
			lexicalPragmaVec.addElement(lexp);
		    }
	        }
		imports.append(cu.imports);
		TypeDeclVec typevec = cu.elems;
		for (int i=0; i<typevec.size(); ++i) {
		    TypeDecl td = typevec.elementAt(i);
		    boolean foundMatch = false;
		    for (int j=0; j<types.size(); ++j) {
			if (types.elementAt(j).id.equals(td.id)) {
			    foundMatch = true;
			    combine(td,types.elementAt(j));
			}
		    }
		    if (!foundMatch) {
			// FIXME _ should we make a copy ???
			types.addElement(td);
		    }
		}
	    }
	    return CompilationUnit.make(pkgName,lexicalPragmaVec,imports,types,loc);
	}
     
	void combineFields(FieldDecl newfd, FieldDecl fd) {
		// FIXME - check, combine modifiers
		fd.modifiers |= newfd.modifiers;
	}

	boolean match(RoutineDecl newrd, RoutineDecl rd) {
	    if ((newrd instanceof MethodDecl) != 
		(rd instanceof MethodDecl)) return false;
	    if ((newrd instanceof ConstructorDecl) != 
		(rd instanceof ConstructorDecl)) return false;
	    if (newrd instanceof MethodDecl) {
		MethodDecl newmd = (MethodDecl)newrd;
		MethodDecl md = (MethodDecl)rd;
		if ( !newmd.id.equals( md.id ) ) return false;
		// FIXME - check reutrn type
	    }
	    if (newrd.args.size() != rd.args.size()) return false;
	    for (int i=0; i<newrd.args.size(); ++i) {
		FormalParaDecl newarg = newrd.args.elementAt(i);
		FormalParaDecl arg = rd.args.elementAt(i);
		// Mismatched id - an error or a non-match???
		if (!(newarg.id.equals(arg.id))) return false;
		// FIXME - check modifiers
		// FIXME - check id
		// FIXME - chech type
	    }
	    return true;
	}

	void combineRoutine(RoutineDecl newrd, RoutineDecl rd) {
	    // FIXME - check exceptions
	    for (int i=0; i<newrd.args.size(); ++i) {
		FormalParaDecl newarg = newrd.args.elementAt(i);
		FormalParaDecl arg = rd.args.elementAt(i);
		// FIXME - combine modifiers
	    }
	    // FIXME - check modifiers ???
	    // combine modifiers
	    rd.modifiers |= newrd.modifiers;

            // add body
	    // FIXME -- body should only come from Java file
            if (rd.body == null) rd.body = newrd.body;

	    // combine pragmas
	    if (rd.pmodifiers == null) {
		rd.pmodifiers = ModifierPragmaVec.make();
	    }
	    if (newrd.pmodifiers != null) rd.pmodifiers.append(newrd.pmodifiers);
	    if (rd.tmodifiers == null) {
		rd.tmodifiers = TypeModifierPragmaVec.make();
	    }
	    if (newrd.tmodifiers != null) rd.tmodifiers.append(newrd.tmodifiers);

	}

	void combine(TypeDecl newtd, TypeDecl td) {
	    // Compare modifiers -- FIXME
	    td.modifiers |= newtd.modifiers;
	    td.specOnly = td.specOnly && newtd.specOnly;

	    // Add to the type's annotations
	    if (td.pmodifiers == null) {
		td.pmodifiers = ModifierPragmaVec.make();
	    }
	    if (newtd.pmodifiers != null) td.pmodifiers.append(newtd.pmodifiers);
	    if (td.tmodifiers == null) {
		td.tmodifiers = TypeModifierPragmaVec.make();
	    }
	    if (newtd.tmodifiers != null) td.tmodifiers.append(newtd.tmodifiers);

	    // Verify that superInterfaces are identical -- FIXME
	    // BVerify that superclass is identical -- FIXME

	    // Check and combine the fields etc. of the type declarations
	    for (int i=0; i<newtd.elems.size(); ++i) {
		TypeDeclElem tde = newtd.elems.elementAt(i);
		boolean found = false;
		if (tde instanceof FieldDecl) {
		    for (int k=0; k<td.elems.size(); ++k) {
			TypeDeclElem tdee = td.elems.elementAt(k);
			if (!(tdee instanceof FieldDecl)) continue;
			if (!( ((FieldDecl)tde).id.equals( ((FieldDecl)tdee).id ))) continue;
			combineFields( (FieldDecl)tde, (FieldDecl)tdee );
			found = true;
		    }
		    if (!found) {
			td.elems.addElement(tde);
			tde.setParent(td);
		    }
		} else if (tde instanceof RoutineDecl) {
		    for (int k=0; k<td.elems.size(); ++k) {
			TypeDeclElem tdee = td.elems.elementAt(k);
			if (!(tdee instanceof RoutineDecl)) continue;
			if (!match( (RoutineDecl)tde, (RoutineDecl)tdee )) continue;
			combineRoutine( (RoutineDecl)tde, (RoutineDecl)tdee );
			found = true;
		    }
		    if (!found) {
			td.elems.addElement(tde);
			tde.setParent(td);
		    }
		} else if (tde instanceof TypeDecl) {
		    for (int k=0; k<td.elems.size(); ++k) {
			TypeDeclElem tdee = td.elems.elementAt(k);
			if (!(tdee instanceof TypeDecl)) continue;
			if ( ((TypeDecl)tde).id.equals( ((TypeDecl)tdee).id)) {
			    combine( (TypeDecl)tde, (TypeDecl)tdee );
			    found = true;
			}
		    }
		    if (!found) {
			td.elems.addElement(tde);
			tde.setParent(td);
		    }
		} else if (tde instanceof InitBlock) {
		    td.elems.addElement(tde);
		    tde.setParent(td);
		} else if (tde instanceof GhostDeclPragma) {
		    GhostDeclPragma g = (GhostDeclPragma)tde;
		    for (int k=0; k<td.elems.size(); ++k) {
			TypeDeclElem tdee = td.elems.elementAt(k);
			if (!(tdee instanceof GhostDeclPragma)) continue;
			if ( ((GhostDeclPragma)tde).decl.id.equals( ((GhostDeclPragma)tdee).decl.id)) {
				// FIXME - check types and modifiers
				// FIXME - what about initializer ???
			    // FIXME - what combining to do???
			    found = true;
			}
		    }
		    if (!found) {
			td.elems.addElement(tde);
			tde.setParent(td);
		    }
		    
		} else if (tde instanceof ModelDeclPragma) {
		    ModelDeclPragma g = (ModelDeclPragma)tde;
		    for (int k=0; k<td.elems.size(); ++k) {
			TypeDeclElem tdee = td.elems.elementAt(k);
			if (!(tdee instanceof ModelDeclPragma)) continue;
			if ( ((ModelDeclPragma)tde).decl.id.equals( ((ModelDeclPragma)tdee).decl.id)) {
				// FIXME - check types and modifiers
			    // FIXME - what combining to do???
			    found = true;
			}
		    }
		    if (!found) {
			td.elems.addElement(tde);
			tde.setParent(td);
		    }
		} else if (tde instanceof ModelMethodDeclPragma) {
		    ModelMethodDeclPragma g = (ModelMethodDeclPragma)tde;
		    for (int k=0; k<td.elems.size(); ++k) {
			TypeDeclElem tdee = td.elems.elementAt(k);
			if (!(tdee instanceof ModelMethodDeclPragma)) continue;
			if (match( ((ModelMethodDeclPragma)tde).decl,
				   ((ModelMethodDeclPragma)tdee).decl)) {
				// FIXME - check types and modifiers
			    // FIXME - what combining to do???
			    found = true;
			}
		    }
		    if (!found) {
			td.elems.addElement(tde);
			tde.setParent(td);
		    }
		    
		} else if (tde instanceof TypeDeclElemPragma) {
		    td.elems.addElement(tde);
		    tde.setParent(td);
		} else {
		    System.out.println("SKIPPED " + tde.getClass());
		}
	    }
	}

        boolean refining = false;

	ArrayList getRefinementSequence(String[] pkgStrings, Identifier type, 
				CompilationUnit cu) {
	    ArrayList refinements = new ArrayList();
	    GenericFile gf = cu.sourceFile();
	    String gfid = gf.getCanonicalID();
	    GenericFile gfile =
		((EscTypeReader)OutsideEnv.reader).findFirst(
			pkgStrings,type.toString());
	    EscTypeReader tr = (EscTypeReader)OutsideEnv.reader;
	    CompilationUnit ccu;
	    boolean found = false;
	    while(gfile != null) {
		//System.out.println("GFILE " + gfile);
		if (gfile.getCanonicalID().equals(gfid)) {
		    // Avoid parsing a file twice
		    ccu = cu;
		    found = true;
                } else {
		    refining = true;
		    ccu = tr.read(gfile,false);
		    refining = false;
		}
		refinements.add(ccu);
		gfile = findRefined(pkgStrings,ccu);
		if (gfile != null) for (int i=0; i<refinements.size(); ++i) {
		    if ( ((CompilationUnit)refinements.get(i)).sourceFile().
			getCanonicalID().equals( gfile.getCanonicalID() )) {
			ErrorSet.error(gfile.getHumanName() + 
				" is circularly referenced in a refinement sequence");
			gfile = null;
			break;
		    }
		}
	    }
	    if (!found) {
		String pkg = cu.pkgName == null ? "" : 
				cu.pkgName.printName() + ".";
		String err;
		if (refinements.size() == 0) {
		    err = "The command-line argument " 
			+ cu.sourceFile().getHumanName()
			+ " was not on the classpath, and hence not in its "
			+ "own refinement sequence";
		} else {
		    err = "The command-line argument " 
			+ cu.sourceFile().getHumanName() 
			+ " was not in the refinement sequence for type " 
			+ pkg + type.toString() + ":";
		    for (int k = 0; k<refinements.size(); ++k) {
			err += " " + ((CompilationUnit)refinements.get(k)).
					sourceFile().getHumanName();
		    }
		}
		ErrorSet.error(err);
		return null;
	    }
	    return refinements;
	}

	public static GenericFile findRefined(String[] pkgStrings, CompilationUnit cu) {
	    LexicalPragmaVec v = cu.lexicalPragmas;
	    for (int i=0; i<v.size(); ++i) {
		if (v.elementAt(i) instanceof RefinePragma) {
		    RefinePragma rp = (RefinePragma)v.elementAt(i);
		    String filename = rp.filename;
		    GenericFile gf = ((EscTypeReader)OutsideEnv.reader).findFile(pkgStrings,filename);
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
	for (int i=0; i<nonJavaSuffixes.length; ++i) {
	    if (javaFileSpace.findFile(P, T, nonJavaSuffixes[i]) != null) {
		return true;
	    }
	}
	return false;
    }

    public GenericFile findFirst(String[] P, String T) {
	return javaFileSpace.findFile(P,T,activeSuffixes);
    }

    public GenericFile findFile(String[] P, String filename) {
	return javaFileSpace.findFile(P,filename);
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
	    GenericFile spec = javaFileSpace.findFile(P, T, nonJavaSuffixes[i]);
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
