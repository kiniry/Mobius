// This class is generated as part os the 2003 Revision of the ESC Tools
// Author: David Cok


package escjava;

import javafe.ast.*;
import javafe.util.ErrorSet;
import javafe.util.Location;
import escjava.ast.*;
import escjava.ast.TagConstants;
import escjava.ast.Modifiers;
import escjava.tc.FlowInsensitiveChecks;
import javafe.tc.Types;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Enumeration;
import java.util.LinkedList;
import java.util.List;

/** This class handles the desugaring of annotations.

*/
public class AnnotationHandler {

    public AnnotationHandler() {}

    protected TypeDecl td = null;

    /** This must be called on a compilation unit to get the model imports
	listed, so that type names used in annotations can be found, and to
	get model methods put into the class's signature.
	It is called as part of EscSrcReader, a subclass of SrcReader, 
	defined in EscTypeReader.
    */
    public void handlePragmas(CompilationUnit cu) {
	if (cu == null) return;
	// move any model imports into the list of imports
	for (int i = 0; i < cu.lexicalPragmas.size(); ++i) {
		LexicalPragma p = cu.lexicalPragmas.elementAt(i);
		if (p instanceof ImportPragma) 
			cu.imports.addElement(((ImportPragma)p).decl);
	}

	TypeDeclVec elems = cu.elems;
	for (int i=0; i<elems.size(); ++i) {
	    TypeDecl td = elems.elementAt(i);
	    handleTypeDecl(td);
	}
    }

    /** After parsing, but before type checking, we need to convert model
	methods to regular methods, so that
	names are resolved correctly; also need to set ACC_PURE bits correctly
	in all classes so that later checks get done correctly.
    */ // FIXME - possibly should put these in GhostEnv??
    public void handleTypeDecl(TypeDecl td) {
	handlePragmas(td);
	for (int j=0; j<td.elems.size(); ++j) {
	    TypeDeclElem tde = td.elems.elementAt(j);
	    // Handle nested types
	    if (tde instanceof TypeDecl) {
		handleTypeDecl((TypeDecl)tde);
	    }
	    // move any model methods into the list of methods
	    if (tde instanceof ModelMethodDeclPragma) {
		handlePragmas(tde);
		ModelMethodDeclPragma mmp = (ModelMethodDeclPragma)tde;
		td.elems.setElementAt(((ModelMethodDeclPragma)tde).decl,j);
	    } else if (tde instanceof ModelConstructorDeclPragma) {
		handlePragmas(tde);
		ModelConstructorDeclPragma mmp = (ModelConstructorDeclPragma)tde;
		if (mmp.id == null) {
		   // An error reported already - improper name cf. EscPragmaParser
		} else if (mmp.id.id != td.id) {
		    ErrorSet.error(mmp.id.getStartLoc(),"A constructor-like declaration has an id which is not the same as the id of the enclosing type: " + mmp.id.id + " vs. " + td.id, td.locId);
		} else {
		    td.elems.setElementAt(((ModelConstructorDeclPragma)tde).decl,j);
		}
	    } else if (tde instanceof ModelTypePragma) {
		handlePragmas(tde);
		ModelTypePragma tdp = (ModelTypePragma)tde;
		td.elems.setElementAt(tdp.decl,j);
	    }
	    // handle PURE pragmas
	    if (tde instanceof MethodDecl ||
		tde instanceof ConstructorDecl) {
		handlePragmas(tde);
	    }
	}
    }

    public void handlePragmas(TypeDeclElem tde) {
	ModifierPragmaVec mpp = 
	    (tde instanceof TypeDecl) ? ((TypeDecl)tde).pmodifiers:
	    (tde instanceof RoutineDecl) ? ((RoutineDecl)tde).pmodifiers :
	    null;

	if (mpp != null) for (int i=0; i<mpp.size(); ++i) {
	    ModifierPragma m = mpp.elementAt(i);
	    if (m.getTag() == TagConstants.PURE) {
		tde.setModifiers(tde.getModifiers() | Modifiers.ACC_PURE);
	    }
	}
    }

    //-----------------------------------------------------------------------
/*
    public void process(TypeDecl td) {
	this.td = td;

	for (int i=0; i<td.elems.size(); ++i) {
	    TypeDeclElem tde = td.elems.elementAt(i);
	    process(tde);
        }
    }
*/

    public void process(TypeDeclElem tde) {
	int tag = tde.getTag();
	switch (tag) {
// What about initially, monitored_by, readable_if clauses ??? FIXME
// What about nested classes ??? FIXME
// What about redundant clauses ??? FIXME


	    case TagConstants.CONSTRUCTORDECL:
	    case TagConstants.METHODDECL:
		process((RoutineDecl)tde);
		break;

	    case TagConstants.FIELDDECL:
		break;

	    case TagConstants.GHOSTDECLPRAGMA:
	    case TagConstants.MODELDECLPRAGMA:
	    case TagConstants.INVARIANT:
	    case TagConstants.INVARIANT_REDUNDANTLY:
	    case TagConstants.CONSTRAINT:
		Context c = new Context();
		c.expr = null; // ((TypeDeclElemPragma)tde).expr;
		(new CheckPurity()).visitNode((ASTNode)tde,c);
		break;

	    case TagConstants.REPRESENTS:
	    case TagConstants.AXIOM:
		(new CheckPurity()).visitNode((ASTNode)tde,null);
		break;

	    case TagConstants.DEPENDS:
	    default:
		//System.out.println("TAG " + tag + " " + TagConstants.toString(tag) + " " + tde.getClass() );
	}

    }

    protected void process(RoutineDecl tde) {
	ModifierPragmaVec pmodifiers = tde.pmodifiers;
	//System.out.println("   Mods " + Modifiers.toString(tde.modifiers));
	if (pmodifiers != null) {
	    for (int i = 0; i<pmodifiers.size(); ++i) {
		ModifierPragma mp = pmodifiers.elementAt(i);
		(new CheckPurity()).visitNode((ASTNode)mp,null);
	    }
	}
    }

    //-----------------------------------------------------------------------
    // Desugaring is done as a last stage of type-checking.  The desugar
    // methods below may presume that all expressions are type-checked.
    // As a result, any constructed expressions must have type information
    // inserted.

    public void desugar(TypeDecl td) {
	int n = td.elems.size();
	for (int i=0; i<n; ++i) {
	    TypeDeclElem tde = td.elems.elementAt(i);
	    if (tde instanceof RoutineDecl) desugar((RoutineDecl)tde);
	    if (tde instanceof TypeDecl) desugar((TypeDecl)tde);
	    // FIXME - what about model routines and types
	}
    }

    public void desugar(RoutineDecl tde) {
	if ((tde.modifiers & Modifiers.ACC_DESUGARED) != 0) return;

	// Now desugar this routine itself

	ModifierPragmaVec pmodifiers = tde.pmodifiers;
	Identifier id =
		tde instanceof MethodDecl ?
			((MethodDecl)tde).id
		: tde.getParent().id;
	javafe.util.Info.out("Desugaring specifications for " + tde.parent.id + "." + id);
	try { // Just for safety's sake
	    tde.pmodifiers = desugarAnnotations(pmodifiers,tde);
	} catch (Exception e) {
	    tde.pmodifiers = ModifierPragmaVec.make();
	    ErrorSet.error(tde.getStartLoc(),
		"Internal error while desugaring annotations: " + e);
	    e.printStackTrace();
	}
	tde.modifiers |=  Modifiers.ACC_DESUGARED;

	if (Main.options().desugaredSpecs) {
	  System.out.println("Desugared specifications for " + tde.parent.id + "." + id);
	    printSpecs(tde);
	}
    }
    static public void printSpecs(RoutineDecl tde) {
	  if (tde.pmodifiers != null)
	   for (int i = 0; i<tde.pmodifiers.size(); ++i) {
	    ModifierPragma mp = tde.pmodifiers.elementAt(i);
		printSpec(mp);
	   }
    }
    static public void printSpec(ModifierPragma mp) {
	    System.out.print("   " + 
		escjava.ast.TagConstants.toString(mp.getTag()) + " "  );
	    if (mp instanceof ExprModifierPragma) {
		ExprModifierPragma mpe = (ExprModifierPragma)mp;
		print(mpe.expr);
	    } else if (mp instanceof CondExprModifierPragma) {
		CondExprModifierPragma mpe = (CondExprModifierPragma)mp;
		print(mpe.expr);
		if (mpe.cond != null) {
		    System.out.print(" if ");
		    print(mpe.cond);
		}
	    } else if (mp instanceof VarExprModifierPragma) {
		VarExprModifierPragma mpe = (VarExprModifierPragma)mp;
		System.out.print("(" + Types.toClassTypeSig(mpe.arg.type).getExternalName()
		    + (mpe.arg.id == TagConstants.ExsuresIdnName ? "" :
			" " + mpe.arg.id.toString()) + ")");
		print(mpe.expr);
	    }
	    System.out.println("");
    }

    protected ModifierPragmaVec desugarAnnotations(ModifierPragmaVec pm,
					    RoutineDecl tde) {
	if (pm == null) {
	    pm = ModifierPragmaVec.make();
	}

	ModifierPragmaVec newpm = ModifierPragmaVec.make();

	boolean isPure = FlowInsensitiveChecks.isPure(tde);
	boolean isConstructor = tde instanceof ConstructorDecl;

	// Get non_null specs
	ModifierPragmaVec nonnullBehavior = getNonNull(tde);

	javafe.util.Set overrideSet = null;
	if (!isConstructor) overrideSet = FlowInsensitiveChecks.getDirectOverrides((MethodDecl)tde);

	boolean overrides = !isConstructor && !overrideSet.isEmpty();
	

	if (!overrides && nonnullBehavior.size()==0) {
	    // Add a default 'requires true' clause if there are no
	    // specs at all and the routine is not overriding anything
//if (tde instanceof MethodDecl)
//System.out.println("QQQ " +  ((MethodDecl)tde).id + " " + overrides + " " + nonnullBehavior.size() + " " + pm.size());
	    boolean doit = pm.size() == 0;
	    if (!doit) {
		// Need to determine if there are any clause specs
		doit = true;
		ModifierPragma mpp = pm.elementAt(pm.size()-1);
		if (mpp instanceof ParsedSpecs) {
//System.out.println("QRR " + ((ParsedSpecs)mpp).specs.specs.size());
		    doit = ((ParsedSpecs)mpp).specs.specs.size() == 0;
		}
		else doit = false;
// FIXME - why do we get ExprModifierPragmas here (e.g. test8)
//System.out.println("QT " + mpp.getClass());
	    }
	    if (doit) {
		ExprModifierPragma e = ExprModifierPragma.make(
			TagConstants.REQUIRES, T, Location.NULL);
		newpm.addElement(e);
		newpm.addElement(defaultModifies(Location.NULL,T,tde));
	    }
	}


	RoutineDecl previousDecl = null;
	int pos = 0;
	while (pos < pm.size()) {
	    ModifierPragma p = pm.elementAt(pos++);
	    if (p.getTag() == TagConstants.PARSEDSPECS) {
		ParsedSpecs ps = (ParsedSpecs)p;
		previousDecl = ps.decl;
		if (overrides && ps.specs.initialAlso == null && ps.specs.specs.size() != 0) {
		    ErrorSet.caution(ps.getStartLoc(),"JML requires a specification to begin with 'also' when the method overrides other methods" ,((MethodDecl)overrideSet.elements().nextElement()).locType);
		}
		if (!overrides && ps.specs.initialAlso != null) {
		    if (!(tde.parent instanceof InterfaceDecl)) {
			ErrorSet.caution(ps.specs.initialAlso.getStartLoc(),
			    "No initial also expected since there are no overridden or refined methods");
		    } else {
			MethodDecl omd = Types.javaLangObject().hasMethod(
				((MethodDecl)tde).id, tde.argTypes());
			if (omd == null || Modifiers.isPrivate(omd.modifiers) )
			    ErrorSet.caution(ps.specs.initialAlso.getStartLoc(),
				"No initial also expected since there are no overridden or refined methods");
		    }
		}
		break;
	    }
	}
	while (pos < pm.size()) {
	    ModifierPragma p = pm.elementAt(pos++);
	    if (p.getTag() == TagConstants.PARSEDSPECS) {
		ParsedSpecs ps = (ParsedSpecs)p;
		if (ps.specs.initialAlso == null && ps.specs.specs.size() != 0) {
		    ErrorSet.caution(ps.getStartLoc(),
			"JML requires a specification to begin with 'also' when the declaration refines a previous declaration",previousDecl.locId);
		}
		previousDecl = ps.decl;
	    }
	}


	ParsedRoutineSpecs accumulatedSpecs = new ParsedRoutineSpecs();
	pos = 0;
	while (pos < pm.size()) {
	    ModifierPragma p = pm.elementAt(pos++);
	    if (p.getTag() == TagConstants.PARSEDSPECS) {
		ParsedRoutineSpecs ps = ((ParsedSpecs)p).specs;
		ParsedRoutineSpecs newps = new ParsedRoutineSpecs();
		deNest(ps.specs,nonnullBehavior,newps.specs);
		deNest(ps.impliesThat,nonnullBehavior, newps.impliesThat);
		deNest(ps.examples,nonnullBehavior, newps.examples);
		accumulatedSpecs.specs.addAll(newps.specs);
		accumulatedSpecs.impliesThat.addAll(newps.impliesThat);
		accumulatedSpecs.examples.addAll(newps.examples);
	    } else {
		newpm.addElement(p);
	    }
	}
	ModifierPragmaVec r = desugar(accumulatedSpecs.specs, tde);
	// accumulatedSpecs.impliesThat = desugar(accumulatedSpecs.impliesThat);
	// accumulatedSpecs.examples = desugar(accumulatedSpecs.examples); // FIXME - not doing this because we are not doing anything with the result.
	newpm.append(r);
	return newpm;
    }

	// NOTE: If we do desugaring after typechecking, we need to put in 
	// all of the types for the expressions we construct.  If we do
	// desugaring before typechecking, we do not, or we risk not 
	// checking any of the details of that expression. Currently
	// desugaring comes first. 

    public ModifierPragmaVec getNonNull(RoutineDecl rd) {
	ModifierPragmaVec result = ModifierPragmaVec.make(2);
	FormalParaDeclVec args = rd.args;

	// Check that non_null on parameters is allowed
	if (rd instanceof MethodDecl) {
	    MethodDecl md = (MethodDecl)rd;
	    // Need to check all overrides, because we may not have processed a
	    // given direct override yet, removing its spurious non_null
	    javafe.util.Set overrides = FlowInsensitiveChecks.getAllOverrides(md);
	    if (overrides != null && !overrides.isEmpty()) {
		for (int i=0; i<args.size(); ++i) {
		    FormalParaDecl arg = args.elementAt(i);
		    ModifierPragma m = Utils.findModifierPragma(arg,TagConstants.NON_NULL);
		    if (m != null) { // overriding method has non_null for parameter i
			MethodDecl smd = FlowInsensitiveChecks.getSuperNonNullStatus(md,i,overrides);
			if (smd != null) { // overridden method does not have non_null for i
			    FormalParaDecl sf = smd.args.elementAt(i);
			    ErrorSet.caution(m.getStartLoc(),
				    "The non_null annotation is ignored because this method overrides a method declaration in which this parameter is not declared non_null: ",sf.getStartLoc());
			    Utils.removeModifierPragma(arg,TagConstants.NON_NULL);
			}
		    }
		}
	    }
	}

	// Handle non_null on any parameter
	for (int i=0; i<args.size(); ++i) {
	    FormalParaDecl arg = args.elementAt(i);
	    ModifierPragma m = Utils.findModifierPragma(arg.pmodifiers,TagConstants.NON_NULL);
	    if (m == null) continue;
	    int locNN = m.getStartLoc();
	    result.addElement(
		ExprModifierPragma.make(TagConstants.REQUIRES,
			NonNullExpr.make(arg,locNN),
			locNN)
		);
	}

	// Handle non_null on the result
	ModifierPragma m = Utils.findModifierPragma(rd.pmodifiers,TagConstants.NON_NULL);
	if (m != null) {
	    int locNN = m.getStartLoc();
	    Expr r = ResExpr.make(locNN);
	    javafe.tc.FlowInsensitiveChecks.setType(r, ((MethodDecl)rd).returnType);
	    Expr n = LiteralExpr.make(TagConstants.NULLLIT, null, locNN);
	    javafe.tc.FlowInsensitiveChecks.setType(n, Types.nullType);
	    Expr e = BinaryExpr.make(TagConstants.NE, r, n, locNN);
	    javafe.tc.FlowInsensitiveChecks.setType(e, Types.booleanType);
	    ExprModifierPragma emp = ExprModifierPragma.make(TagConstants.ENSURES, e, locNN);
	    emp.errorTag = TagConstants.CHKNONNULLRESULT;
	    result.addElement(emp);
	}
	return result;
    }

/*
public static void psprint(ArrayList ps) {
	if (ps == null) {System.out.println("PS IS NULL"); return;}
System.out.println("START PS " + ps.size());
Iterator i = ps.iterator();
while (i.hasNext()) {
	Object o = i.next();
	System.out.println("ELEM " + o.getClass());
	if (o instanceof ModifierPragmaVec) psprint((ModifierPragmaVec)o);
}
System.out.println("END PS");
}

public static void psprint(ModifierPragmaVec mp) {
if (mp == null) { System.out.println("MPV IS NULL"); return; }
System.out.println("MPV " + mp.size());
for (int i=0; i<mp.size(); ++i) {
ModifierPragma m = mp.elementAt(i);
System.out.println("MPV-ELEM " + TagConstants.toString(m.getTag()));
if (m instanceof ParsedSpecs) {
	ArrayList a = ((ParsedSpecs)m).specs.specs;
	psprint(a);
}
}
System.out.println("END_MPV");
}
*/

	// Argument is an ArrayList of ModifierPragmaVec corresponding to
	// also-connected de-nested specification cases
	// result is a single ModifierPragmaVec with all the requires
	// clauses combined and all the other clauses guarded by the 
	// relevant precondition
    public ModifierPragmaVec desugar(ArrayList ps, RoutineDecl tde) {
	ArrayList requiresList = new ArrayList();
	ModifierPragmaVec resultList = ModifierPragmaVec.make();
	resultList.addElement(null); // replaced below
	Iterator i = ps.iterator();
	while (i.hasNext()) {
	    ModifierPragmaVec m = (ModifierPragmaVec)i.next();
	    desugar(m,requiresList,resultList,tde);
	}
	// combine all of the requires
	ExprModifierPragma requires = or(requiresList);
	resultList.setElementAt(requires,0);
	if (requires == null) resultList.removeElementAt(0);
	return resultList;
    }

	// requiresList is an ArrayList of ModifierPragma
    public void desugar(ModifierPragmaVec m,ArrayList requiresList,
			ModifierPragmaVec resultList, RoutineDecl tde){
	GenericVarDeclVec foralls = GenericVarDeclVec.make();
	// First collect all the requires clauses together
	int pos = 0;
	ArrayList list = new ArrayList();
	while (pos < m.size()) {
	    ModifierPragma mp = m.elementAt(pos++);
	    int tag = mp.getTag();
	    if (tag == TagConstants.NO_WACK_FORALL) foralls.addElement(
			((VarDeclModifierPragma)mp).decl );
	    if (tag != TagConstants.REQUIRES &&
		tag != TagConstants.PRECONDITION) continue;
	    if (((ExprModifierPragma)mp).expr.getTag() 
			== TagConstants.NOTSPECIFIEDEXPR) continue;
	    list.add(forallWrap(foralls,mp));
	}
	ExprModifierPragma conjunction = and(list);
	boolean reqIsTrue = conjunction == null || isTrue(conjunction.expr);
	boolean reqIsFalse = conjunction != null && isFalse(conjunction.expr);
	Expr reqexpr = conjunction==null? null : conjunction.expr;
//System.out.println("REQ " + reqexpr);
	Expr req = T;
	if (reqexpr != null) {
	    ExprVec arg = ExprVec.make(new Expr[]{reqexpr});
	    //req = UnaryExpr.make(TagConstants.PRE, reqexpr, Location.NULL);

	    req = NaryExpr.make(Location.NULL,
				reqexpr.getStartLoc(),TagConstants.PRE,
				Identifier.intern("\\old"),arg);
	    javafe.tc.FlowInsensitiveChecks.setType(req, Types.booleanType);
	}

	if (reqIsTrue && m.size() == 0) return;

	requiresList.add(reqIsTrue? 
		ExprModifierPragma.make(TagConstants.REQUIRES,T,Location.NULL) 
		: andLabeled(list)); 

	// Now transform each non-requires pragma
	boolean foundDiverges = false;
	boolean foundModifies = false;
	pos = 0;
	while (pos < m.size()) {
	    ModifierPragma mp = m.elementAt(pos++);
	    int tag = mp.getTag();
	    if (tag == TagConstants.REQUIRES ||
		tag == TagConstants.PRECONDITION) continue;
	    switch (tag) {
		case TagConstants.DIVERGES:
		    foundDiverges = true;
		    // fall-through
		case TagConstants.ENSURES:
		case TagConstants.POSTCONDITION:
		case TagConstants.WHEN:
		{
		    ExprModifierPragma mm = (ExprModifierPragma)mp;
		    if (mm.expr.getTag() == TagConstants.NOTSPECIFIEDEXPR)
			break;
		    if (!reqIsTrue) mm.expr = implies(req,mm.expr);
		    resultList.addElement(mm);
		    break;
		}

		case TagConstants.SIGNALS:
		case TagConstants.EXSURES:
		{
		    VarExprModifierPragma mm = (VarExprModifierPragma)mp;
		    if (mm.expr.getTag() == TagConstants.NOTSPECIFIEDEXPR)
			break;
		    if (!reqIsTrue) mm.expr = implies(req,mm.expr);
		    resultList.addElement(mm);
		    break;
		}
		case TagConstants.MODIFIES:
		case TagConstants.MODIFIABLE:
		case TagConstants.ASSIGNABLE:
		    foundModifies = true;
		    // fall-through
		case TagConstants.WORKING_SPACE:
		case TagConstants.DURATION:
		  {
		    CondExprModifierPragma mm = (CondExprModifierPragma)mp;
		    if (mm.expr != null &&
		        mm.expr.getTag() == TagConstants.NOTSPECIFIEDEXPR)
			break;
		    mm.cond = and(mm.cond,req);
		    resultList.addElement(mm);
		    break;
		  }

		case TagConstants.ACCESSIBLE:
		case TagConstants.CALLABLE:
		case TagConstants.MEASURED_BY:
		case TagConstants.MODEL_PROGRAM:
			// Remember to skip if not specified
			// FIXME - not yet handled
		    break;

		case TagConstants.NO_WACK_FORALL:
		case TagConstants.OLD:
		    // These are handled elsewhere and don't get put into
		    // the pragma list.
		    break;

		case TagConstants.MONITORED_BY:
		    ErrorSet.error(mp.getStartLoc(),"monitored_by is obsolete and only applies to fields");
		    break;

		case TagConstants.MONITORED:
		    ErrorSet.error(mp.getStartLoc(),"monitored only applies to fields");
		    break;

		default:
		    ErrorSet.error(mp.getStartLoc(),"Unknown kind of pragma for a routine declaration: " + TagConstants.toString(tag));
		    break;
	    }
	}
	if (!foundDiverges) {
	    // lightweight default - req ==> true which is true
	    // heavyweight default - req ==> false which is !req
	    // The lightweight default need not be added since it does
	    // not need any verification.
/* FIXME - don't need this for now, but need to be sure that when it is 
added, it doesn't change whether a routine appears to have a spec or not.
	    resultList.addElement(ExprModifierPragma.make(
		TagConstants.DIVERGES,implies(req,AnnotationHandler.F),
			Location.NULL));
*/
// FIXME - Null location above and below needs to be fixed.
// Also other use of defaultModifies
// Diverges expression depends on lightweight or heavyweight
	}
	if (!foundModifies) {
	    resultList.addElement(defaultModifies(Location.NULL,req,tde));
	}
    }
    public final static CondExprModifierPragma defaultModifies(int loc, 
				Expr req, RoutineDecl rd) {
	boolean everythingIsDefault = false; // FIXME - eventually change to true
	boolean nothing = !everythingIsDefault;
	boolean isPure = FlowInsensitiveChecks.isPure(rd);

	if (isPure) nothing = true;
	if (isPure && rd instanceof ConstructorDecl) nothing = true; // FIXME - this is wrong - should be this.*
	// FIXME - need default for COnstructor, ModelConstructor
	return CondExprModifierPragma.make(
		TagConstants.MODIFIES,
		nothing ? (Expr)NothingExpr.make(loc) :
			    (Expr)EverythingExpr.make(loc),
		loc,req);
    }


    public ModifierPragma forallWrap(GenericVarDeclVec foralls, 
					ModifierPragma mp) {
	if (mp instanceof ExprModifierPragma) {
		ExprModifierPragma emp = (ExprModifierPragma)mp;
		emp.expr = forallWrap(foralls, emp.expr) ;
		FlowInsensitiveChecks.setType(emp.expr,Types.booleanType);	
	}
	return mp;
    }

    public Expr forallWrap(GenericVarDeclVec foralls, Expr e) {
	if (foralls.size() == 0) return e;
	int loc = foralls.elementAt(0).getStartLoc();
	int endLoc = foralls.elementAt(foralls.size()-1).getStartLoc();
	return QuantifiedExpr.make(loc,endLoc,TagConstants.FORALL,
		foralls,e,null);
    }

    public void deNest(ArrayList ps, ModifierPragmaVec prefix, ArrayList deNestedSpecs) {
	if (ps.size() == 0 && prefix.size() != 0) {
	    deNestedSpecs.add(prefix);
	} else {
	    Iterator i = ps.iterator();
	    while (i.hasNext()) {
		ModifierPragmaVec m = (ModifierPragmaVec)i.next();
		deNest(m,prefix,deNestedSpecs);
	    }
	}
    }

    //@ requires (* m.size() > 0 *);
    // Uses the fact that if there is a nesting it is the last element of
    // the ModifierPragmaVec
    public void deNest(ModifierPragmaVec m, ModifierPragmaVec prefix, ArrayList deNestedSpecs) {
	ModifierPragma last = m.elementAt(m.size()-1);
	if (last instanceof NestedModifierPragma) {
	    m.removeElementAt(m.size()-1);
	    ModifierPragmaVec newprefix = prefix.copy();
	    newprefix.append(m);
	    m.addElement(last);
	    ArrayList list = ((NestedModifierPragma)last).list;
	    deNest(list,newprefix,deNestedSpecs);
	} else {
	    ModifierPragmaVec mm = prefix.copy();
	    mm.append(m);
	    deNestedSpecs.add(mm);
	}
    }
/*
    public int deNest(boolean exampleMode, int pos, ModifierPragmaVec pm, ArrayList results, Behavior cb, boolean isPure, boolean isConstructor) {
	Behavior currentBehavior = cb.copy(); // new Behavior();
	LinkedList commonBehavior = new LinkedList();
	ModifierPragma m = null;
	boolean terminate = false;
	while (!terminate) {
	    m = pm.elementAt(pos++);
	    int t = m.getTag();
	    //System.out.println("GOT TAG " + TagConstants.toString(t));
	    switch (t) {
		case TagConstants.BEHAVIOR:
		    if (exampleMode)
			ErrorSet.error("Behavior keyword should not be used in examples section - use example");
		    currentBehavior = cb.copy(); //new Behavior();
		    currentBehavior.isLightweight = false;
		    break;
		case TagConstants.EXAMPLE:
		    if (!exampleMode)
			ErrorSet.error("Example keyword should not be used outside the examples section - use behavior");
		    currentBehavior = new Behavior();
		    currentBehavior.isLightweight = false;
		    break;

		case TagConstants.NORMAL_BEHAVIOR:
		    if (exampleMode)
			ErrorSet.error("normal_behavior keyword should not be used in examples section - use normal_example");
		    currentBehavior = cb.copy(); //new Behavior();
		    currentBehavior.isLightweight = false;
		    currentBehavior.isNormal = true;
		    // set a false signals clause
		    currentBehavior.signals.add(Behavior.defaultSignalFalse(
				m.getStartLoc()));
		    break;

		case TagConstants.NORMAL_EXAMPLE:
		    if (!exampleMode)
			ErrorSet.error("normal_example keyword should not be used outside the examples section - use normal_behavior");
		    currentBehavior = new Behavior();
		    currentBehavior.isLightweight = false;
		    currentBehavior.isNormal = true;
		    // set a false signals clause
		    currentBehavior.signals.add(Behavior.defaultSignalFalse(
				m.getStartLoc()));
		    break;

		case TagConstants.EXCEPTIONAL_BEHAVIOR:
		    if (exampleMode)
			ErrorSet.error("exceptional_behavior keyword should not be used in examples section - use exceptional_example");
		    currentBehavior = cb.copy(); // new Behavior();
		    currentBehavior.isLightweight = false;
		    currentBehavior.isExceptional = true;
		    // set a false ensures clause
		    currentBehavior.ensures.add(Behavior.ensuresFalse(m.getStartLoc()));
		    break;

		case TagConstants.EXCEPTIONAL_EXAMPLE:
		    if (!exampleMode)
			ErrorSet.error("exceptional_example keyword should not be used outside the examples section - use exceptional_behavior");
		    currentBehavior = new Behavior();
		    currentBehavior.isLightweight = false;
		    currentBehavior.isExceptional = true;
		    // set a false ensures clause
		    currentBehavior.ensures.add(Behavior.ensuresFalse(m.getStartLoc()));
		    break;

                // All redundant tokens should not exist in the AST
                // anymore; they are represented with redundant fields in
                // the AST nodes.
		case TagConstants.DIVERGES_REDUNDANTLY:
		case TagConstants.ENSURES_REDUNDANTLY:
		case TagConstants.EXSURES_REDUNDANTLY:
		case TagConstants.REQUIRES_REDUNDANTLY:
		case TagConstants.SIGNALS_REDUNDANTLY:
                    assert false : "Redundant keywords should not be in AST!";
                    break;

		case TagConstants.REQUIRES:
		case TagConstants.ALSO_REQUIRES:
		case TagConstants.PRECONDITION: {
		    if (currentBehavior == null) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); // new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
		    ExprModifierPragma e = (ExprModifierPragma)m;
		    if (e.expr.getTag() != TagConstants.NOTSPECIFIEDEXPR)
			currentBehavior.requires.add(e);
		    break;
		}
		    
		case TagConstants.ENSURES:
		case TagConstants.ALSO_ENSURES:
		case TagConstants.POSTCONDITION: {
		    if (currentBehavior == null) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); // new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
		    if (currentBehavior.isExceptional) {
			ErrorSet.error(m.getStartLoc(),
			   "This type of annotation is not permitted in an excpetional_behavior clause");
		    }
		    ExprModifierPragma e = (ExprModifierPragma)m;
		    if (e.expr.getTag() != TagConstants.NOTSPECIFIEDEXPR)
			currentBehavior.ensures.add(e);
		    break;
		 }

		case TagConstants.DIVERGES:
		    if (currentBehavior == null) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); // new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
		    ExprModifierPragma e = (ExprModifierPragma)m;
		    if (e.expr.getTag() != TagConstants.NOTSPECIFIEDEXPR)
			currentBehavior.diverges.add(e);
		    break;

		case TagConstants.EXSURES:
		case TagConstants.ALSO_EXSURES:
		case TagConstants.SIGNALS:
		    if (currentBehavior == null) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); //  new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
		    if (currentBehavior.isNormal) {
			ErrorSet.error(m.getStartLoc(),
			   "This type of annotation is not permitted in an normal_behavior clause");
		    }
		    if (((VarExprModifierPragma)m).expr.getTag() != TagConstants.NOTSPECIFIEDEXPR)
			currentBehavior.signals.add(m);
		    break;

		case TagConstants.ASSIGNABLE:
		case TagConstants.MODIFIABLE:
		case TagConstants.MODIFIES:
		case TagConstants.ALSO_MODIFIES: {
		    if (currentBehavior == null) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); // new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
			// null value indicates an informal annotation
		    if (((CondExprModifierPragma)m).expr == null ||
		    	((CondExprModifierPragma)m).expr.getTag() != 
				TagConstants.NOTSPECIFIEDEXPR)
			currentBehavior.modifies.add(m);
		    if (isPure && !isConstructor) {
			CondExprModifierPragma cm = 
				(CondExprModifierPragma)m;
			if (! ( cm.expr instanceof NothingExpr &&
				cm.cond == null)) {
			    ErrorSet.error(m.getStartLoc(),
			     "A pure method may not have an assignable clause");
			}
		    }
			// FIXME - for constructors, should check that 
			//  the assignable clause has only the allowed stuff.
		    break;
		}

		case TagConstants.WHEN:
		    if (currentBehavior == null) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); //new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
		    if (((ExprModifierPragma)m).expr.getTag() != 
					TagConstants.NOTSPECIFIEDEXPR)
			currentBehavior.when.add(m);
		    break;

		case TagConstants.DURATION:
		case TagConstants.WORKING_SPACE:
		    if (currentBehavior == null) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); //new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
		    if (((CondExprModifierPragma)m).expr.getTag() != 
					TagConstants.NOTSPECIFIEDEXPR) {
			if (t == TagConstants.DURATION)
			    currentBehavior.duration.add(m);
			else
			    currentBehavior.workingSpace.add(m);
		    }
		    break;

		case TagConstants.OPENPRAGMA:
		    if (currentBehavior == null) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); // new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
		    currentBehavior.openPragma = m;
		    commonBehavior.addFirst(currentBehavior.copy());
		    break;

		case TagConstants.ALSO:
		    if (currentBehavior != null) 
			results.add(currentBehavior);
		    if (commonBehavior.isEmpty()) {
			currentBehavior = cb.copy(); // new Behavior();
		    } else {
			currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
		    }
		    break;

		case TagConstants.CLOSEPRAGMA:
		    if (currentBehavior != null) 
			results.add(currentBehavior);
		    if (commonBehavior.isEmpty()) {
			ErrorSet.error(m.getStartLoc(),
			    "Encountered |} without a matching {|");
		    } else {
			commonBehavior.removeFirst();
			currentBehavior = null;
		    }
		    break;

		case TagConstants.MODEL_PROGRAM:
		    if (currentBehavior == null && !currentBehavior.isEmpty()) {
			ErrorSet.error(m.getStartLoc(),"Missing also");
			if (commonBehavior.isEmpty()) {
			    currentBehavior = cb.copy(); // new Behavior();
			} else {
			    currentBehavior = ((Behavior)commonBehavior.getFirst()).copy();
			}
		    }
		    if (!commonBehavior.isEmpty()) {
			ErrorSet.error(m.getStartLoc(),
			     "A model program may not be nested");
		    }
		    // FIXME - the model programs aren't saved anywhere
		    currentBehavior = null;
		    break;

		case TagConstants.SUBCLASSING_CONTRACT:
		    if (exampleMode)
			ErrorSet.error(m.getStartLoc(),
			      "Misplaced subclassing_contract clause");
		    --pos;
		    terminate = true;
		    break; 

		case TagConstants.IMPLIES_THAT:
		    if (exampleMode) 
			ErrorSet.error("Did not expect implies_that after examples section");
		    // fall through
		case TagConstants.FOR_EXAMPLE:
		case TagConstants.ALSO_REFINE:
		case TagConstants.END:
		    --pos;
		    terminate = true;
		    break; 

		case TagConstants.SPEC_PUBLIC:
		case TagConstants.SPEC_PROTECTED:
		case TagConstants.PURE:
		case TagConstants.NON_NULL:
		case TagConstants.HELPER:
		case TagConstants.INSTANCE:
		    if (currentBehavior == null) 
				currentBehavior = new Behavior();
		    currentBehavior.extras.add(m);
		    continue; 

	 	case TagConstants.GHOST:
		case TagConstants.MODEL:
		    break;

	        default:

		    ErrorSet.caution(m.getStartLoc(),
			"Desugaring does not support "
			+ TagConstants.toString(m.getTag()));

		    currentBehavior.extras.add(m);
		    break;
            }
        } 
	if (currentBehavior != null) {
	    if (currentBehavior.isEmpty()) {
	    } else {
		results.add(currentBehavior);
	    }
	}
	if (!commonBehavior.isEmpty()) {
	    ModifierPragma openPragma = ((Behavior)commonBehavior.getFirst()).openPragma;
	    ErrorSet.error(openPragma.getStartLoc(),"No closing |} for this {|");
	}
	return pos;
    }
*/
/*
    public int sc_section(int pos, ModifierPragmaVec pm, ArrayList results) {
	while (pos < pm.size()) {
	    ModifierPragma m = pm.elementAt(pos++);
	    switch (m.getTag()) {
		case TagConstants.ACCESSIBLE:
		case TagConstants.CALLABLE:
		case TagConstants.MEASURED_BY:
		    results.add(m);
		    break;

		case TagConstants.IMPLIES_THAT:
		case TagConstants.FOR_EXAMPLE:
		case TagConstants.END:
		case TagConstants.PURE:
		case TagConstants.NON_NULL:
		    return pos-1;

		default:
		    ErrorSet.error("Did not expect this annotation in a subclassing_contract");
	    }
	}
	return pos;
    }
*/
    /** Produces an expression which is the conjunction of the two expressions.
	If either input is null, the other is returned.  If either input is
	literally true or false, the appropriate constant folding is performed.
    */
    static public Expr and(Expr e1, Expr e2) {
	if (e1 == null || isTrue(e1)) return e2;
	if (e2 == null || isTrue(e2)) return e1;
	if (isFalse(e1)) return e1;
	if (isFalse(e2)) return e2;
	Expr e = BinaryExpr.make(TagConstants.AND,e1,e2,e1.getStartLoc());
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return e;
    }

    /** Produces an ExprModifierPragma whose expression is the conjunction 
	of the expressions in the input pragmas.
	If either input is null, the other is returned.  If either input is
	literally true or false, the appropriate constant folding is performed.
    */
    static public ExprModifierPragma and(ExprModifierPragma e1, ExprModifierPragma e2) {
	if (e1 == null || isTrue(e1.expr)) return e2;
	if (e2 == null || isTrue(e2.expr)) return e1;
	if (isFalse(e1.expr)) return e1;
	if (isFalse(e2.expr)) return e2;
	Expr e = BinaryExpr.make(TagConstants.AND,e1.expr,e2.expr,e1.getStartLoc());
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return ExprModifierPragma.make(
			e1.getTag(),e,e1.getStartLoc());
    }

    /** Produces an ExprModifierPragma whose expression is the conjunction of
	all of the expressions in the ExprModifierPragmas in the argument.
	If the argument is empty, null is returned.  Otherwise, some
	object is returned, though its expression might be a literal.
    */
    static public ExprModifierPragma and(/*@ non_null */ ArrayList a) {
	if (a.size() == 0) {
	    return null;
	} else if (a.size() == 1) {
	    return (ExprModifierPragma)a.get(0);
	} else {
	    ExprModifierPragma e = null;
	    Iterator i = a.iterator();
	    while (i.hasNext()) {
		e = and(e,(ExprModifierPragma)i.next());
	    }
	    return e;
	}
    }

    /** The same as and(ArrayList), but produces labelled expressions within
	the conjunction so that error messages come out with useful locations.
    */
    static public ExprModifierPragma andLabeled(/*@ non_null */ ArrayList a) {
	if (a.size() == 0) {
	    return null;
	} else {
	    Expr e = null;
	    int floc = Location.NULL;
	    Iterator i = a.iterator();
	    while (i.hasNext()) {
		ExprModifierPragma emp = (ExprModifierPragma)i.next();
		int loc = emp.getStartLoc();
		if (floc == Location.NULL) floc = loc;
		boolean nn = emp.expr instanceof NonNullExpr;
		Expr le = LabelExpr.make(
				emp.getStartLoc(), emp.getEndLoc(), false, 
				escjava.translate.GC.makeFullLabel(
					nn?"NonNull":"Pre",loc,Location.NULL),
				emp.expr);
		javafe.tc.FlowInsensitiveChecks.setType(le,Types.booleanType);
		if (!isTrue(emp.expr)) e = and(e, le);
		else if (e == null) e = le;
		javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	    }
	    return ExprModifierPragma.make(TagConstants.REQUIRES,
			e, floc);
	}
    }
/*
    static public Expr or(Expr e1, Expr e2) {
	if (e1 == null || isFalse(e1)) return e2;
	if (e2 == null || isFalse(e2)) return e1;
	if (isTrue(e1)) return e1;
	if (isTrue(e2)) return e2;
	Expr e = BinaryExpr.make(TagConstants.OR,e1,e2,e1.getStartLoc());
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return e;
    }
*/
    /** Produces an ExprModifierPragma whose expression is the disjunction 
	of the expressions in the input pragmas.
	If either input is null, the other is returned.  If either input is
	literally true or false, the appropriate constant folding is performed.
    */
    static public ExprModifierPragma or(ExprModifierPragma e1, ExprModifierPragma e2) {
	if (e1 == null || isFalse(e1.expr)) return e2;
	if (e2 == null || isFalse(e2.expr)) return e1;
	if (isTrue(e1.expr)) return e1;
	if (isTrue(e2.expr)) return e2;
	Expr e = BinaryExpr.make(TagConstants.OR,e1.expr,e2.expr,e1.getStartLoc());
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return ExprModifierPragma.make(
			e1.getTag(),e,e1.getStartLoc());
    }

    /** Produces an ExprModifierPragma whose expression is the disjunction of
	all of the expressions in the ExprModifierPragmas in the argument.
	If the argument is empty, null is returned.  Otherwise, some
	object is returned, though its expression might be a literal.
    */
    static public ExprModifierPragma or(/*@ non_null */ ArrayList a) {
	if (a.size() == 0) {
	    return null;
	} else if (a.size() == 1) {
	    return (ExprModifierPragma)a.get(0);
	} else {
	    ExprModifierPragma e = null;
	    Iterator i = a.iterator();
	    while (i.hasNext()) {
		e = or(e,(ExprModifierPragma)i.next());
	    }
	    return e;
	}
    }

    /** Produces an expression which is the implication of the two expressions.
	Neither input may be null.  If either input is
	literally true or false, the appropriate constant folding is performed.
    */
    static public Expr implies(/*@ non_null */Expr e1, /*@ non_null */ Expr e2) {
	if (isTrue(e1)) return e2;
	if (isTrue(e2)) return e2; // Use e2 instead of T to keep location info 
	if (isFalse(e1)) return T;
	Expr e = BinaryExpr.make(TagConstants.IMPLIES,e1,e2,e2.getStartLoc());
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return e;
    }

    /** Returns true if the argument is literally true, and returns
	false if it is not a literal or is literally false. */
    static boolean isTrue(/*@ non_null */ Expr e) {
	return e == T || 
	    (e instanceof LiteralExpr && 
		((LiteralExpr)e).value.equals(T.value));
    }

    /** Returns true if the argument is literally false, and returns
	false if it is not a literal or is literally true. */
    static boolean isFalse(/*@ non_null */ Expr e) {
	return e == F || 
	    (e instanceof LiteralExpr && 
		((LiteralExpr)e).value.equals(F.value));
    }

    public final static LiteralExpr T = 
	    (LiteralExpr)FlowInsensitiveChecks.setType(LiteralExpr.make(
	    TagConstants.BOOLEANLIT, Boolean.TRUE, Location.NULL),
	    Types.booleanType);
    public final static LiteralExpr F = 
	    (LiteralExpr)FlowInsensitiveChecks.setType(LiteralExpr.make(
	    TagConstants.BOOLEANLIT, Boolean.FALSE, Location.NULL),
	    Types.booleanType);

    static public class Context {
	public Expr expr;
	

    }

    static public class CheckPurity {

	public void visitNode(ASTNode x, Context cc) {
	    if (x == null) return;
//System.out.println("CP TAG " + TagConstants.toString(x.getTag()));
	    switch (x.getTag()) {
		case TagConstants.METHODINVOCATION:
		    MethodInvocation m = (MethodInvocation)x;
		    if (Main.options().checkPurity &&
		        !FlowInsensitiveChecks.isPure(m.decl)) {
			ErrorSet.error(m.locId,
			    "Method " + m.id + " is used in an annotation" +
			    " but is not pure (" + 
			    Location.toFileLineString(m.decl.loc) + ")");
		    }
		    break;
		case TagConstants.NEWINSTANCEEXPR:
		    NewInstanceExpr c = (NewInstanceExpr)x;
		    if (Main.options().checkPurity &&
		        !FlowInsensitiveChecks.isPure(c.decl)) {
			ErrorSet.error(c.loc,
			    "Constructor is used in an annotation" +
			    " but is not pure (" + 
			    Location.toFileLineString(c.decl.loc) + ")");
		    }
		    break;
		case TagConstants.WACK_DURATION:
		case TagConstants.WACK_WORKING_SPACE:
		case TagConstants.SPACE:
		    // The argument of these built-in functions is not
		    // evaluated, so it need not be pure.
		    return;

		case TagConstants.ENSURES:
		case TagConstants.POSTCONDITION:
		case TagConstants.REQUIRES:
		case TagConstants.PRECONDITION:
		{
		    Context cn = new Context();
		    cn.expr = ((ExprModifierPragma)x).expr;
		    visitNode(cn.expr,cn);
		    ((ExprModifierPragma)x).expr = cn.expr;
		    return;
		}
	
		case TagConstants.SIGNALS:
		case TagConstants.EXSURES:

		    break;
	    }
	    {
		    int n = x.childCount();
		    for (int i = 0; i < n; ++i) {
			if (x.childAt(i) instanceof ASTNode)
				visitNode((ASTNode)x.childAt(i),cc);
		    }
	    }
	}

    }



    static private void print(Expr e) {
	if (e != null) PrettyPrint.inst.print(System.out,0,e);
    }

    static public class NonNullExpr extends BinaryExpr {

	static NonNullExpr make(FormalParaDecl arg, int locNN) {
	    NonNullExpr e = new NonNullExpr();
	    int loc = arg.getStartLoc();
	    Expr v = VariableAccess.make(arg.id, loc, arg);
	    javafe.tc.FlowInsensitiveChecks.setType(v, arg.type);
	    Expr n = LiteralExpr.make(TagConstants.NULLLIT, null, locNN);
	    javafe.tc.FlowInsensitiveChecks.setType(n, Types.nullType);
	    e.op = TagConstants.NE;
	    e.left = v;
	    e.right = n;
	    e.locOp = locNN;
	    javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	    return e;
	}
    }

    //----------------------------------------------------------------------
    // Parsing the sequence of ModifierPragmas for each method of a 
    // compilation unit happens as a part of the original parsing and
    // refinement processing.

    static NestedPragmaParser specparser = new NestedPragmaParser();

    public void parseAllRoutineSpecs(CompilationUnit ccu) {
	specparser.parseAllRoutineSpecs(ccu);
    }
		




/** The routines in this class parse a sequence of ModifierPragma that 
    occur prior to a method or constructor declaration.  These consist
    of lightwieght or heavywieght specifications, possibly nested or
    with consecutive spec-cases separated by 'also'.  The parsing of the
    compilation unit simply produces a flat sequence of such ModifierPragmas,
    since they may occur in separate annotation comments and the Javafe
    parser does not provide mechanisms to associate them together.
    However, we do need to determine the nesting structure of the sequence
    of pragmas because the forall and old pragmas introduce new variable
    declarations that may be used in subsequent pragmas.  This parsing into
    the nested structure (and checking of it) needs to be completed prior
    to type checking so that the variable references are properly 
    determined.  The ultimate desugaring then happens after typechecking.

    The resulting pmodifiers vector for each routine consists of a
    possibly-empty sequence of simple routine modifiers (e.g. pure, non_null)
    terminated with a single ParsedSpecs element.
 */    

static public class NestedPragmaParser {
 
    /** Parses the sequence of pragma modifiers for each routine in 
	the CompilationUnit,
	replacing the existing sequence with the parsed one in each case.
    */
    public void parseAllRoutineSpecs(CompilationUnit ccu) {
        TypeDeclVec v = ccu.elems;
        for (int i=0; i<v.size(); ++i) {
            parseAllRoutineSpecs(v.elementAt(i));
        }
    }
 
    public void parseAllRoutineSpecs(TypeDecl td) {
        TypeDeclElemVec v = td.elems;
        for (int i=0; i<v.size(); ++i) {
            TypeDeclElem tde = v.elementAt(i);
            if (tde instanceof RoutineDecl) {
                parseRoutineSpecs((RoutineDecl)tde);
            } else if (tde instanceof ModelMethodDeclPragma) {
                parseRoutineSpecs( ((ModelMethodDeclPragma)tde).decl );
            } else if (tde instanceof ModelConstructorDeclPragma) {
                parseRoutineSpecs( ((ModelConstructorDeclPragma)tde).decl );
            } else if (tde instanceof TypeDecl) {
                parseAllRoutineSpecs((TypeDecl)tde);
            }
        }
    }
 
    public void parseRoutineSpecs(RoutineDecl rd) {
        ModifierPragmaVec pm = rd.pmodifiers;
        if (pm == null || pm.size() == 0) {
	    ParsedRoutineSpecs pms = new ParsedRoutineSpecs();
	    pms.modifiers.addElement(ParsedSpecs.make(rd,pms));
	    rd.pmodifiers = pms.modifiers;
	    return;
	}
	if (pm.elementAt(pm.size()-1) instanceof ParsedSpecs) {
	    // It is a bit of a design problem that the parsing of the
	    // sequence of pragmas produces a new ModifierPragmaVec that
	    // overwrites the old one.  That means that if we call 
	    // parseRoutineSpecs twice on a routine we get problems.
	    // This test is here to avoid problems if a bug elsewhere
	    // causes this to happen.
	    // In fact there currently is such a bug - if the same type is
	    // listed more than once on the command-line, the refinement
	    // file list gets redetermined and the files within it are
	    // parsed a second time.  That may be fixed by the time you
	    // read this, but until then...
	    System.out.println("OUCH - attempt to reparse " + Location.toString(rd.getStartLoc()));
javafe.util.ErrorSet.dump("OUCH");
	    return;
	}

	// We add this (internal use only) END pragma so that we don't have
	// to continually check the value of pos vs. the size of the array
	pm.addElement(SimpleModifierPragma.make(TagConstants.END,
			pm.size() == 0 ? Location.NULL :
			pm.elementAt(pm.size()-1).getStartLoc()));

        ParsedRoutineSpecs pms = new ParsedRoutineSpecs();
        int pos = 0;
        if (pm.elementAt(0).getTag() == TagConstants.ALSO) {
                pms.initialAlso = pm.elementAt(0);
                ++pos;
        }
        pos = parseAlsoSeq(pos,pm,1,null,pms.specs);
        if (pm.elementAt(pos).getTag() == TagConstants.IMPLIES_THAT) {
	    ++pos;
            pos = parseAlsoSeq(pos,pm,1,null,pms.impliesThat);
        }
        if (pm.elementAt(pos).getTag() == TagConstants.FOR_EXAMPLE) {
	    ++pos;
            pos = parseAlsoSeq(pos,pm,2,null,pms.examples);
        }
        if (pm.elementAt(pos).getTag() == TagConstants.IMPLIES_THAT) {
	    ErrorSet.caution(pm.elementAt(pos).getStartLoc(),
		"implies_that sections are expected to precede for_example sections");
	    ++pos;
            pos = parseAlsoSeq(pos,pm,1,null,pms.impliesThat);
        }
        while (true) {
            ModifierPragma mp = pm.elementAt(pos);
            int tag = mp.getTag();
            if (tag == TagConstants.END) break;
		// Turned off because of problems with annotations after the declaration - FIXME
            if (false && !isRoutineModifier(tag)) {
                int loc = Location.NULL;
                if (pms.modifiers.size() > 0)
                    loc = pms.modifiers.elementAt(0).getStartLoc();
                ErrorSet.error(mp.getStartLoc(),
                    "Unexpected or out of order pragma (expected a simple routine modifier)",loc);
            } else {
                pms.modifiers.addElement(mp);
            }
	    ++pos;
        }
	pms.modifiers.addElement(ParsedSpecs.make(rd,pms));
	rd.pmodifiers = pms.modifiers;
    }
 
    static public boolean isRoutineModifier(int tag) {
        return tag == TagConstants.PURE ||
                tag == TagConstants.SPEC_PUBLIC ||
                tag == TagConstants.SPEC_PROTECTED ||
                tag == TagConstants.HELPER ||
                tag == TagConstants.GHOST || // Actually should not occur
                tag == TagConstants.MODEL ||
                tag == TagConstants.MONITORED ||
                tag == TagConstants.FUNCTION ||
                tag == TagConstants.NON_NULL;
    }
 
    // behaviorMode == 0 : nested call
    // behaviorMode == 1 : outer call - non-example mode, model programs allowed
    // behaviorMode == 2 : outer call - example mode
    // The behaviorMode is used to determine which behavior/example keywords
    // are valid - but this is only needed on the outermost nesting level.
    // The behaviorTag is used to determine whether signals or ensures clauses
    // are permitted; 0 means either are ok; not valid on outermost call
    public int parseAlsoSeq(int pos, ModifierPragmaVec pm, 
		    int behaviorMode, ModifierPragma behavior, ArrayList result) {
        while(true) {
          ModifierPragmaVec mpv = ModifierPragmaVec.make();
	  if (behaviorMode != 0) {
	    ModifierPragma mp = pm.elementAt(pos);
	    behavior = mp;
	    int behaviorTag = mp.getTag();
	    ++pos;
	    encounteredError = false;
	    switch (behaviorTag) {
		case TagConstants.MODEL_PROGRAM:
		    if (behaviorMode == 2) {
			ErrorSet.error(mp.getStartLoc(),
			"Model programs may not be in the examples section");
			encounteredError = true;
		    } else if (pm.elementAt(pos).getTag() != TagConstants.ALSO
		      && pm.elementAt(pos).getTag() != TagConstants.END) {
			ErrorSet.error(mp.getStartLoc(),
			    "A model_program may not be combined with other clauses");
		    } else {
			mpv.addElement(mp);
			result.add(mpv);
			break;
		    }
		    continue;

		case TagConstants.BEHAVIOR:
		    if (behaviorMode == 2) ErrorSet.error(mp.getStartLoc(),
			"Behavior keywords may not be in the for_example section");
		    break;
		case TagConstants.NORMAL_BEHAVIOR:
		    if (behaviorMode == 2) ErrorSet.error(mp.getStartLoc(),
			"Behavior keywords may not be in the for_example section");
		    mpv.addElement(VarExprModifierPragma.make(
			    TagConstants.SIGNALS,
			    FormalParaDecl.make(0,null,
				TagConstants.ExsuresIdnName,
				Types.javaLangException(),mp.getStartLoc()),
			    AnnotationHandler.F,
			    mp.getStartLoc()));
		    break;
		case TagConstants.EXCEPTIONAL_BEHAVIOR:
		    if (behaviorMode == 2) ErrorSet.error(mp.getStartLoc(),
			"Behavior keywords may not be in the for_example section");
		    mpv.addElement(
			ExprModifierPragma.make(TagConstants.ENSURES,
				AnnotationHandler.F, mp.getStartLoc()));
		    break;
		case TagConstants.EXAMPLE:
		    if (behaviorMode == 1) ErrorSet.error(mp.getStartLoc(),
			"Example keywords may be used only in the for_example section");
		    break;
		case TagConstants.NORMAL_EXAMPLE:
		    if (behaviorMode == 1) ErrorSet.error(mp.getStartLoc(),
			"Example keywords may be used only in the for_example section");
		    mpv.addElement(VarExprModifierPragma.make(
			    TagConstants.SIGNALS,
			    FormalParaDecl.make(0,null,
				TagConstants.ExsuresIdnName,
				Types.javaLangException(),mp.getStartLoc()),
			    AnnotationHandler.F,
			    mp.getStartLoc()));
		    break;
		case TagConstants.EXCEPTIONAL_EXAMPLE:
		    if (behaviorMode == 1) ErrorSet.error(mp.getStartLoc(),
			"Example keywords may be used only in the for_example section");
		    mpv.addElement(
			ExprModifierPragma.make(TagConstants.ENSURES,
				AnnotationHandler.F, mp.getStartLoc()));
		    break;
		default:
		    // lightweight
		    --pos;
		    behavior = null;
	      }
	    }
	    pos = parseSeq(pos,pm,0,behavior,mpv);
            if (mpv.size() != 0) result.add(mpv);
	    else if (behaviorMode == 0 || result.size() != 0) {
		if (!encounteredError) 
		    ErrorSet.error(pm.elementAt(pos).getStartLoc(),
			"JML does not allow empty clause sequences");
		encounteredError = false;
	    }
            if (pm.elementAt(pos).getTag() != TagConstants.ALSO) break;
            ++pos;
        }
	if (behaviorMode != 0) {
	    while (pm.elementAt(pos).getTag() == TagConstants.CLOSEPRAGMA) {
		ErrorSet.error(pm.elementAt(pos).getStartLoc(),
			"There is no opening {| to match this closing |}");
		++pos;
	    }
	}
	return pos;
    }

    private boolean encounteredError;
 
    //@ requires (* pm.elementAt(pm.size()-1).getTag() == TagConstants.END *);
    public int parseSeq(int pos, ModifierPragmaVec pm, 
			int behaviorMode, ModifierPragma behavior, 
			ModifierPragmaVec result) {
	int behaviorTag = behavior==null? 0 : behavior.getTag();
	//System.out.println("STARTING " + behaviorMode + " " + behaviorTag);
	if (pm.elementAt(pos).getTag() == TagConstants.MODEL_PROGRAM) {
	    if (behaviorMode == 0) {
		ErrorSet.error(pm.elementAt(pos).getStartLoc(),
		    "Model programs may not be nested");
		encounteredError = true;
	    }
	    ++pos;
	}
        while (true) {
            ModifierPragma mp = pm.elementAt(pos);
	    int loc = mp.getStartLoc();
            int tag = mp.getTag();
            if (isRoutineModifier(tag)) return pos;
	    //System.out.println("TAG " + TagConstants.toString(tag));
            switch (tag) {
                case TagConstants.END:
                case TagConstants.IMPLIES_THAT:
                case TagConstants.FOR_EXAMPLE:
                case TagConstants.ALSO:
                case TagConstants.CLOSEPRAGMA:
                    return pos;

		case TagConstants.MODEL_PROGRAM:
		    ErrorSet.error(mp.getStartLoc(),
			 "Model programs may not be combined with other clauses");
		    ++pos;
		    break;

		case TagConstants.BEHAVIOR:
		case TagConstants.NORMAL_BEHAVIOR:
		case TagConstants.EXCEPTIONAL_BEHAVIOR:
		case TagConstants.EXAMPLE:
		case TagConstants.NORMAL_EXAMPLE:
		case TagConstants.EXCEPTIONAL_EXAMPLE:
		    if (behaviorMode == 0) ErrorSet.error(mp.getStartLoc(),
			"Misplaced " + TagConstants.toString(tag) + " keyword");
		    ++pos;
		    break;
 
                case TagConstants.OPENPRAGMA:
                  {
                    int openLoc = loc;
                    ++pos;
		    ArrayList s = new ArrayList();
                    pos = parseAlsoSeq(pos,pm,0,behavior,s);
                    if (pm.elementAt(pos).getTag() != TagConstants.CLOSEPRAGMA) {
                        ErrorSet.error(pm.elementAt(pos).getStartLoc(),
                            "Expected a closing |}",openLoc);
                    } else {
			++pos;
		    }
		    // Empty sequences are noted in parseAlsoSeq
		    if (s.size() != 0) {
			result.addElement(NestedModifierPragma.make(s));
		    }
                  }
		  break;

		// Any clause keyword ends up in the default (as well as
		// anything unrecognized).  We do that because there are
		// so many clause keywords.  However, that means that we
		// have to be sure to have the list of keywords in 
		// isRoutineModifier correct.
                default:
		    if (
			(((behaviorTag == TagConstants.NORMAL_BEHAVIOR ||
			behaviorTag == TagConstants.NORMAL_EXAMPLE) &&
			(tag == TagConstants.SIGNALS ||
			 tag == TagConstants.EXSURES))) 
			||
			(((behaviorTag == TagConstants.EXCEPTIONAL_BEHAVIOR ||
			behaviorTag == TagConstants.EXCEPTIONAL_EXAMPLE) &&
			(tag == TagConstants.ENSURES ||
			 tag == TagConstants.POSTCONDITION))) 
			) {
			ErrorSet.error(loc,"A " + TagConstants.toString(tag) +
			    " clause is not allowed in a " +
			    TagConstants.toString(behaviorTag) + " section",
			    behavior.getStartLoc());
		    } else {
			result.addElement(mp);
		    }
		    ++pos;
            }
        }
    }
}

    public static List findRepresents(FieldDecl fd) {
	List results = new LinkedList();
	TypeDecl td = fd.parent;
	TypeDeclElemVec tdepv = td.elems;
	for (int i=0; i<tdepv.size(); ++i) {
	    TypeDeclElem tde = tdepv.elementAt(i);
	    if (!(tde instanceof TypeDeclElemPragma)) continue;
	    if (tde.getTag() != TagConstants.REPRESENTS) continue;
	    Expr target = ((NamedExprDeclPragma)tde).target;
	    if (!(target instanceof FieldAccess)) continue; // ERROR - FIXME
	    FieldDecl fdd = ((FieldAccess)target).decl;
	    if (fd != fdd) continue;
	    results.add( ((NamedExprDeclPragma)tde).expr );
	}	
	return results;
    }
}
// FIXME - things not checked
//	There should be no clauses after a |} (only |} only also or END or simple mods)
//	The order of clauses is not checked
//	JML only allows forall, old, requires prior to a nesting.
