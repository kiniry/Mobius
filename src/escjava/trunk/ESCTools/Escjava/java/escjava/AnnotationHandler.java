// This class is generated as part of the 2003 Revision of the ESC Tools
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
import javafe.tc.TypeSig;

import java.util.ArrayList;
import java.util.Iterator;
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
// 	javafe.util.Info.out("Desugaring specifications for " + tde.parent.id + "." + id);

// 	if (Main.options().desugaredSpecs) {
//             System.out.println("Desugaring specifications for " + tde.parent.id + "." + id);
//             printSpecs(tde);
//             System.out.println("\n");
// 	}

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
	    if (mp instanceof ModifiesGroupPragma) {
		EscPrettyPrint.inst.print(System.out,0,(ModifiesGroupPragma)mp);
		System.out.println("");
		return;
	    }
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
	    } else {
		EscPrettyPrint.inst.print(System.out,0,mp);
	    }
	    System.out.println("");
    }

    protected ModifierPragmaVec desugarAnnotations(ModifierPragmaVec pm,
					    RoutineDecl tde) {
	if (pm == null) {
	    pm = ModifierPragmaVec.make();
	}

	ModifierPragmaVec newpm = ModifierPragmaVec.make();

	//boolean isPure = Utils.isPure(tde);
	boolean isConstructor = tde instanceof ConstructorDecl;

	// Get non_null specs
	ModifierPragmaVec nonnullBehavior = getNonNull(tde);

	javafe.util.Set overrideSet = null;
	if (!isConstructor) overrideSet = FlowInsensitiveChecks.getDirectOverrides((MethodDecl)tde);

	boolean overrides = !isConstructor && !overrideSet.isEmpty();
	

	boolean defaultSpecs = false;
	if (!overrides && nonnullBehavior.size()==0) {
	    // Add a default 'requires true' clause if there are no
	    // specs at all and the routine is not overriding anything
	    boolean doit = pm.size() == 0;
	    if (!doit) {
		// Need to determine if there are any clause specs
		doit = true;
		int k = pm.size();
		while ((--k)>=0) {
		    ModifierPragma mpp = pm.elementAt(k);
		    if (!(mpp instanceof ParsedSpecs)) {
			break;
		    }
		    if (((ParsedSpecs)mpp).specs.specs.size() != 0) {
			doit = false;
			break;
		    }
		}
// FIXME - why do we get ExprModifierPragmas here (e.g. test8)
//System.out.println("QT " + mpp.getClass());
	    }
	    if (doit) {
		defaultSpecs = true;
		ExprModifierPragma e = ExprModifierPragma.make(
		    TagConstants.REQUIRES, T, tde.getStartLoc());
		newpm.addElement(e);
		newpm.addElement(defaultModifies(tde.getStartLoc(),T,tde));
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
	if (defaultSpecs && (tde instanceof ConstructorDecl) && tde.implicit) {
	    TypeSig td = TypeSig.getSig(tde.parent);
	    TypeSig tds = td.superClass();
	    if (tds != null && tde.pmodifiers != null && 
			tde.pmodifiers.size() > 0) try {
		ConstructorDecl cd = tds.lookupConstructor(new Type[0],td);
		desugar(cd);
		// Only remove previous elements after successfully finding
		// a parent constructor
		newpm.removeAllElements();
		ModifierPragmaVec mp = cd.pmodifiers;
		for (int i=0; i<mp.size(); ++i) {
		    ModifierPragma m = mp.elementAt(i);
		    int t = m.getTag();
		    if (t == TagConstants.REQUIRES ||
			t == TagConstants.PRECONDITION ||
			t == TagConstants.MODIFIESGROUPPRAGMA ||
			t == TagConstants.MODIFIES ||
			t == TagConstants.ASSIGNABLE) {
			newpm.addElement(m);
		    }
		}
	    } catch (Exception e) {
		// Purposely ignore this
	    }
	}
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
	//boolean reqIsFalse = conjunction != null && isFalse(conjunction.expr);
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
		    if (mm.expr.getTag() == TagConstants.INFORMALPRED_TOKEN)
			break;
		    if (isTrue(mm.expr)) break;
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
		    if (mm.expr.getTag() == TagConstants.INFORMALPRED_TOKEN)
			break;
		    if (isTrue(mm.expr)) break;
		    if (!reqIsTrue) mm.expr = implies(req,mm.expr);
		    resultList.addElement(mm);
		    break;
		}
		case TagConstants.MODIFIESGROUPPRAGMA:
		  {
		    foundModifies = true;
		    ModifiesGroupPragma mm = (ModifiesGroupPragma)mp;
		    mm.precondition = req;
		    resultList.addElement(mm);
		    break;
		  }
/*
		case TagConstants.MODIFIES:
		case TagConstants.MODIFIABLE:
		case TagConstants.ASSIGNABLE:
		  {
		    CondExprModifierPragma mm = (CondExprModifierPragma)mp;
		    if (mm.expr != null &&
		        mm.expr.getTag() == TagConstants.NOTSPECIFIEDEXPR)
			break;
		    foundModifies = true;
		    mm.cond = and(mm.cond,req);
		    resultList.addElement(mm);
		    break;
		  }
*/

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
		case TagConstants.CODE_CONTRACT:
			// Remember to skip if not specified
			// FIXME - not yet handled
		    foundModifies = true; // Don't add a default modifies
		    foundDiverges = true;
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
/* FIXME - don't need this for now, but need to be sure that when it is 
added, it doesn't change whether a routine appears to have a spec or not.
	if (!foundDiverges) {
	    // lightweight default - req ==> true which is true
	    // heavyweight default - req ==> false which is !req
	    // The lightweight default need not be added since it does
	    // not need any verification.
	    resultList.addElement(ExprModifierPragma.make(
		TagConstants.DIVERGES,implies(req,AnnotationHandler.F),
			Location.NULL));
// FIXME - Null location above and below needs to be fixed.
// Also other use of defaultModifies
// Diverges expression depends on lightweight or heavyweight
	}
*/
	if (!foundModifies) {
	    resultList.addElement(defaultModifies(tde.getStartLoc(),req,tde));
	}
    }
    public final static ModifiesGroupPragma defaultModifies(int loc, 
				Expr req, RoutineDecl rd) {
	boolean everythingIsDefault = true;
	boolean nothing = !everythingIsDefault;
	boolean isPure = Utils.isPure(rd);

	if (isPure) nothing = true;
	Expr e;
	if (isPure && rd instanceof ConstructorDecl) {
	    ExprObjectDesignator eod = 
		ExprObjectDesignator.make(loc,ThisExpr.make(null,loc));
	    FlowInsensitiveChecks.setType(eod.expr,TypeSig.getSig(rd.parent));
	    e = WildRefExpr.make(null,eod);
	} else if (nothing) {
	    e = NothingExpr.make(loc);
	} else {
	    e = EverythingExpr.make(loc);
	}

	// FIXME - need default for COnstructor, ModelConstructor
	ModifiesGroupPragma r = ModifiesGroupPragma.make(
					TagConstants.MODIFIES,loc);
	r.addElement( CondExprModifierPragma.make(
		TagConstants.MODIFIES,e,loc,req));
	r.precondition = req;
	return r;
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
		foralls,null,e,null,null);
    }

    public void deNest(ArrayList ps, ModifierPragmaVec prefix, ArrayList deNestedSpecs) {
	if (ps.size() == 0 && prefix.size() != 0) {
	    combineModifies(prefix);
	    deNestedSpecs.add(prefix);
	} else {
	    Iterator i = ps.iterator();
	    while (i.hasNext()) {
		ModifierPragmaVec m = (ModifierPragmaVec)i.next();
		deNest(m,prefix,deNestedSpecs);
	    }
	}
    }

    public void combineModifies(ModifierPragmaVec list) {
	ModifiesGroupPragma m = null;
	for (int i=0; i<list.size(); ++i) {
	    ModifierPragma mp = list.elementAt(i);
	    if (mp.getTag() == TagConstants.MODIFIESGROUPPRAGMA) {
		ModifiesGroupPragma mm = (ModifiesGroupPragma)mp;
		if (m == null) m = mm;
		else {
		    m.append(mm);
		    list.removeElementAt(i);
		    --i;
		}
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
	    combineModifies(mm);
	    deNestedSpecs.add(mm);
	}
    }

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
			nn?"NonNull":"Pre",loc,Location.NULL), // FIXME - does this get translated to include an @ location ?
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
		        !Utils.isPure(m.decl)) {
			ErrorSet.error(m.locId,
			    "Method " + m.id + " is used in an annotation" +
			    " but is not pure (" + 
			    Location.toFileLineString(m.decl.loc) + ")");
		    }
		    break;
		case TagConstants.NEWINSTANCEEXPR:
		    NewInstanceExpr c = (NewInstanceExpr)x;
		    if (Main.options().checkPurity &&
		        !Utils.isPure(c.decl)) {
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

    static public boolean isEndingModifier(int tag) {
	return tag == TagConstants.END ||
		tag == TagConstants.ALSO ||
		tag == TagConstants.IMPLIES_THAT ||
		tag == TagConstants.FOR_EXAMPLE;
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
		    } else if (!isEndingModifier(pm.elementAt(pos).getTag()) && 
				!isRoutineModifier(pm.elementAt(pos).getTag()) ) {
			ErrorSet.error(mp.getStartLoc(),
			    "A model_program may not be combined with other clauses");
		    } else {
			mpv.addElement(mp);
			result.add(mpv);
			break;
		    }
		    continue;
		case TagConstants.CODE_CONTRACT:
		    if (behaviorMode == 2) {
			ErrorSet.error(mp.getStartLoc(),
			"code_contract sections may not be in an examples section");
			encounteredError = true;
		    } else {
			// FIXME - code_contract sections are ignored for now
			ModifierPragmaVec r = ModifierPragmaVec.make();
			pos = parseCCSeq(pos,pm,r);
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
 
    /** Parse the clauses in a code_contract section */
    public int parseCCSeq(int pos, ModifierPragmaVec pm, ModifierPragmaVec result) {
	boolean badCCSection = false;
	while (true) {
	    ModifierPragma mp = pm.elementAt(pos);
	    int loc = mp.getStartLoc();
	    int tag = mp.getTag();
	    // System.out.println("TAG " + TagConstants.toString(tag));
	    if (isRoutineModifier(tag)) return pos;
	    switch (tag) {
		case TagConstants.END:
		case TagConstants.IMPLIES_THAT:
		case TagConstants.FOR_EXAMPLE:
		case TagConstants.ALSO:
		    return pos;

		case TagConstants.ACCESSIBLE:
		case TagConstants.CALLABLE:
		case TagConstants.MEASURED_BY:
		    result.addElement(mp);
		    ++pos;
		    break;

		default:
		    if (!badCCSection) // Just one error message
			ErrorSet.error(loc,"Unexpected pragma in a code_contract section");
		    badCCSection = true;
		    ++pos;
		    break;
	    }
	} 
    }

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
	if (pm.elementAt(pos).getTag() == TagConstants.CODE_CONTRACT) {
	    if (behaviorMode == 0) {
		ErrorSet.error(pm.elementAt(pos).getStartLoc(),
		    "code_contract sections may not be nested");
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

		case TagConstants.CODE_CONTRACT:
		    ErrorSet.error(mp.getStartLoc(),
			 "code_contract sections may not be combined with other clauses");
		    ++pos;
		    break;

		case TagConstants.ACCESSIBLE:
		case TagConstants.CALLABLE:
		case TagConstants.MEASURED_BY:
		    ErrorSet.error(mp.getStartLoc(),
			"This clause may only be in a code_contract section");
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
	    if (!(target instanceof FieldAccess)) {
		ErrorSet.error(tde.getStartLoc(),
		    "INTERNAL ERROR: Expected FieldAccess here");
		continue;
	    }
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
