// This class is generated as part os the 2003 Revision of the ESC Tools
// Author: David Cok


package escjava;

import javafe.ast.*;
import javafe.util.ErrorSet;
import javafe.util.Location;
import escjava.ast.*;
import escjava.ast.TagConstants;
import escjava.ast.Modifiers;
import escjava.translate.GetSpec;
import escjava.tc.FlowInsensitiveChecks;
import javafe.tc.Types;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Enumeration;
import java.util.LinkedList;

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
	methods to regular methods (with the MODEL modifier bit set), so that
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
	    }
	    if (tde instanceof ModelConstructorDeclPragma) {
		handlePragmas(tde);
		ModelConstructorDeclPragma mmp = (ModelConstructorDeclPragma)tde;
		td.elems.setElementAt(((ModelConstructorDeclPragma)tde).decl,j);
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

    public void process(TypeDecl td) {
	this.td = td;

	for (int i=0; i<td.elems.size(); ++i) {
	    TypeDeclElem tde = td.elems.elementAt(i);
	    process(tde);
        }
    }

    protected void process(TypeDeclElem tde) {
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
	    case TagConstants.REPRESENTS:
	    case TagConstants.AXIOM:
	    case TagConstants.DEPENDS:
		(new CheckPurity()).visitNode((ASTNode)tde);
		break;

	    default:
		//System.out.println("TAG " + tag + " " + TagConstants.toString(tag) + " " + tde.getClass() );
	}

    }

    protected void process(RoutineDecl tde) {
	ModifierPragmaVec pmodifiers = tde.pmodifiers;
	//System.out.println("Method " + (tde instanceof MethodDecl ? ((MethodDecl)tde).id.toString() : "Constructor"));
	//System.out.println("   Mods " + Modifiers.toString(tde.modifiers));
	if (pmodifiers != null) {
	    for (int i = 0; i<pmodifiers.size(); ++i) {
		ModifierPragma mp = pmodifiers.elementAt(i);
		(new CheckPurity()).visitNode((ASTNode)mp);
	    }
	}
	//desugar(tde);
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
		if (mpe.arg == null) {
		    System.out.print( "java.lang.Exception ##  :");
		} else {
		    System.out.print(((TypeName)mpe.arg.type).name.printName() 
			+ " ## " + mpe.arg.id + " : ");
	  	}
		print(mpe.expr);
	    }
	    System.out.println("");
    }

    protected ModifierPragmaVec desugarAnnotations(ModifierPragmaVec pm,
					    RoutineDecl tde) {
	if (pm == null) {
	    pm = ModifierPragmaVec.make();
	}
	java.util.ArrayList newpm = new java.util.ArrayList();

	boolean isPure = escjava.tc.FlowInsensitiveChecks.isPure(tde);
	boolean isConstructor = tde instanceof ConstructorDecl;

	// Get non_null specs
	Behavior nonnullBehavior = getNonNull(tde);

	javafe.util.Set overrideSet = null;
	if (!isConstructor) overrideSet = escjava.tc.FlowInsensitiveChecks.getDirectOverrides((MethodDecl)tde);
	boolean overrides = !isConstructor && !overrideSet.isEmpty();
	
	if (pm.size() == 0 && !overrides && nonnullBehavior.isEmpty()) {
		// No specs at all and no overridden methods.
		ExprModifierPragma e = ExprModifierPragma.make(
			TagConstants.REQUIRES, Behavior.T, Location.NULL);
		pm.addElement(e);
	}

	// We add this (internal use only) END pragma so that we don't have
	// to continually check the value of pos vs. the size of the array
	pm.addElement(SimpleModifierPragma.make(TagConstants.END,
			pm.size() == 0 ? Location.NULL :
			pm.elementAt(pm.size()-1).getStartLoc()));

	int pos = 0;

	// check for an initial also
	ModifierPragma m = pm.elementAt(pos);
	if (m.getTag() == TagConstants.ALSO) {
	    newpm.add(m);
	    ++pos;
	    if (!overrides)
		ErrorSet.caution(m.getStartLoc(),
		    "JML does not permit a specification to begin with 'also' when the method does not override anything");
	} else if (overrides && pm.size() > 1) {
	    // Check if all of the modifiers are pure, helper, non_null, END
	    for (int q=0; q<pm.size(); ++q) {
		int tag = pm.elementAt(q).getTag();
		if (! (tag==TagConstants.PURE || tag == TagConstants.NON_NULL
		  || tag == TagConstants.HELPER || tag == TagConstants.END)) {
			MethodDecl ex = (MethodDecl)(overrideSet.elements().nextElement());
	    		ErrorSet.caution(pm.elementAt(0).getStartLoc(),"JML requires a specification to begin with 'also' when the method overrides other methods (e.g. " + Location.toString(ex.getStartLoc()) + ")");
			break;
		}
	    }
	}

	Behavior accumulatedBehavior = new Behavior();



	// The results array holds the denested spec-cases obtained from
	// parsing the specification of the routine
	ArrayList results = new ArrayList();
	do {

	pos = deNest(false,pos,pm,results,nonnullBehavior,isPure,isConstructor);
	if (pm.elementAt(pos).getTag() == TagConstants.SUBCLASSING_CONTRACT) {
	    ++pos;
	    pos = sc_section(pos,pm,accumulatedBehavior.subclassingContracts);
	}
	if (pm.elementAt(pos).getTag() == TagConstants.IMPLIES_THAT) {
	    ++pos;
	    pos = deNest(false,pos,pm,accumulatedBehavior.implications,new Behavior(),isPure,isConstructor);
	}
	if (pm.elementAt(pos).getTag() == TagConstants.FOR_EXAMPLE) {
	    ++pos;
	    pos = deNest(true,pos,pm,accumulatedBehavior.examples,new Behavior(),isPure,isConstructor);
	}
	if (pm.elementAt(pos).getTag() == TagConstants.ALSO_REFINE) {
	    ++pos;
	    continue;
	}
	while (pm.elementAt(pos).getTag() != TagConstants.END) {
	    ErrorSet.error(pm.elementAt(pos).getStartLoc(),
				"Out of place annotation");
	    ++pos;
	}
	break;
	} while(true);
	
	// Now have to further desugar the annotations that Escjava uses
	// FIXME - adding model programs may require altering this loop
	// Always do the incorporation of the precondition into the
	// postconditions - otherwise desugaring of inheritance does not
	// work soundly.
	{
	    boolean defaultIsModifiesNothing =
		isConstructor && ( ((RoutineDecl)tde).implicit ||
		    javafe.tc.TypeSig.getSig(tde.parent) == javafe.tc.Types.javaLangObject())
		 || escjava.tc.FlowInsensitiveChecks.isPure(tde) ;

	    ArrayList orList = new ArrayList(); // Set of spec-cases to be
				// ored together to form the final clause
	    for (Iterator ii = results.iterator(); ii.hasNext();) {
		Object o = ii.next();
		Behavior b = (Behavior)o;
		b.defaultIsModifiesNothing = defaultIsModifiesNothing;
		accumulatedBehavior.combine(b,orList);
	    }
	    if (orList.isEmpty()) {
		// No groups
		// This should not happen
		accumulatedBehavior.requires = null;
	    } else {
		// Multiple spec cases - have to combine them
		ArrayList newList = new ArrayList();
		boolean trueItem = false;
		Iterator i = orList.iterator();
		while (i.hasNext()) {
		    ArrayList a = (ArrayList)i.next();
		    ExprModifierPragma e = andLabeled(a);
		    if (e != null) newList.add(e);
		    else trueItem = true;
		}
		accumulatedBehavior.requires = new ArrayList();
		if (!trueItem) {
		    ExprModifierPragma ee = or(newList);
		    accumulatedBehavior.requires.add(ee);
		} else {
		    // Need to make a default true requires clause so that
		    // the translation to a VC works correctly
		    ExprModifierPragma ee = 
			ExprModifierPragma.make(TagConstants.REQUIRES,
				Behavior.T, Location.NULL);
		    accumulatedBehavior.requires.add(ee);
		}
	    }
	}

	// End

	if (accumulatedBehavior.requires != null) 
	    newpm.addAll(accumulatedBehavior.requires);

	Iterator ii = accumulatedBehavior.modifies.iterator();
	while (ii.hasNext()) {
	    CondExprModifierPragma e = (CondExprModifierPragma)ii.next();
	    newpm.add(e);
	}
	ii = accumulatedBehavior.ensures.iterator();
	while (ii.hasNext()) {
	    ExprModifierPragma e = (ExprModifierPragma)ii.next();
	    if (e.expr != Behavior.T) newpm.add(e);
	}
	ii = accumulatedBehavior.when.iterator();
	while (ii.hasNext()) {
	    ExprModifierPragma e = (ExprModifierPragma)ii.next();
	    if (e.expr != Behavior.T) newpm.add(e);
	}
	ii = accumulatedBehavior.diverges.iterator();
	while (ii.hasNext()) {
	    ExprModifierPragma e = (ExprModifierPragma)ii.next();
	    if (e.expr != Behavior.T) newpm.add(e);
	}
	ii = accumulatedBehavior.signals.iterator();
	while (ii.hasNext()) {
	    VarExprModifierPragma e = (VarExprModifierPragma)ii.next();
	    newpm.add(e);
	}
	ii = accumulatedBehavior.extras.iterator();
	while (ii.hasNext()) {
	    ModifierPragma e = (ModifierPragma)ii.next();
	    newpm.add(e);
	}


	ModifierPragma[] out = new ModifierPragma[newpm.size()];
	return ModifierPragmaVec.make((ModifierPragma[])(newpm.toArray(out)));
    }

    public Behavior getNonNull(RoutineDecl rd) {
	Behavior b = new Behavior();
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
		    ModifierPragma m = GetSpec.findModifierPragma(arg,TagConstants.NON_NULL);
		    if (m != null) { // overriding method has non_null for parameter i
			MethodDecl smd = FlowInsensitiveChecks.getSuperNonNullStatus(md,i,overrides);
			if (smd != null) { // overridden method does not have non_null for i
			    FormalParaDecl sf = smd.args.elementAt(i);
			    ErrorSet.caution(m.getStartLoc(),
				    "The non_null annotation is ignored because this method overrides a method declaration in which this parameter is not declared non_null: ",sf.getStartLoc());
			    GetSpec.removeModifierPragma(arg,TagConstants.NON_NULL);
			}
		    }
		}
	    }
	}

	// Handle non_null on any parameter
	for (int i=0; i<args.size(); ++i) {
	    FormalParaDecl arg = args.elementAt(i);
	    ModifierPragma m = findModifierPragma(arg.pmodifiers,TagConstants.NON_NULL);
	    if (m == null) continue;
	    int locNN = m.getStartLoc();
	    b.requires.add(
		ExprModifierPragma.make(TagConstants.REQUIRES,
			NonNullExpr.make(arg,locNN),
			locNN)
		);
	}

	// Handle non_null on the result
	ModifierPragma m = findModifierPragma(rd.pmodifiers,TagConstants.NON_NULL);
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
	    b.ensures.add(emp);
	}
	return b;
    }

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
		    currentBehavior.when.add(m);
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
/* This test is not correct or robust - maybe simply allow an empty also?
		//@ if m is null, currentBehavior will not be null
		 if (!results.isEmpty())
			ErrorSet.error(m.getStartLoc(),"Dangling also");
*/
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

    static public Expr and(Expr e1, Expr e2) {
	if (e1 == null || isTrue(e1)) return e2;
	if (e2 == null || isTrue(e2)) return e1;
	if (isFalse(e1)) return e1;
	if (isFalse(e2)) return e2;
	Expr e = BinaryExpr.make(TagConstants.AND,e1,e2,e1.getStartLoc());
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return e;
    }

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

    static public ExprModifierPragma and(ArrayList a) {
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

    static public ExprModifierPragma andLabeled(ArrayList a) {
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
				escjava.translate.GC.makeLabel(
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

    static public Expr or(Expr e1, Expr e2) {
	if (e1 == null || isFalse(e1)) return e2;
	if (e2 == null || isFalse(e2)) return e1;
	if (isTrue(e1)) return e1;
	if (isTrue(e2)) return e2;
	Expr e = BinaryExpr.make(TagConstants.OR,e1,e2,e1.getStartLoc());
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return e;
    }

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

    static public ExprModifierPragma or(ArrayList a) {
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

    static public Expr implies(Expr e1, Expr e2) {
	if (isTrue(e1)) return e2;
	if (isTrue(e2)) return e2; // Use e2 instead of T to keep location info 
	if (isFalse(e1)) return Behavior.T;
	Expr e = BinaryExpr.make(TagConstants.IMPLIES,e1,e2,e2.getStartLoc());
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return e;
    }

    static boolean isTrue(Expr e) {
	return e == Behavior.T || 
	    (e instanceof LiteralExpr && 
		((LiteralExpr)e).value.equals(Behavior.T.value));
    }

    static boolean isFalse(Expr e) {
	return e == Behavior.F || 
	    (e instanceof LiteralExpr && 
		((LiteralExpr)e).value.equals(Behavior.F.value));
    }

    static public class Behavior {

	public final static LiteralExpr T = 
		(LiteralExpr)FlowInsensitiveChecks.setType(LiteralExpr.make(
		TagConstants.BOOLEANLIT, Boolean.TRUE, Location.NULL),
		Types.booleanType);
	public final static LiteralExpr F = 
		(LiteralExpr)FlowInsensitiveChecks.setType(LiteralExpr.make(
		TagConstants.BOOLEANLIT, Boolean.FALSE, Location.NULL),
		Types.booleanType);

	public final static CondExprModifierPragma defaultModifies(int loc, boolean nothing) {
			return CondExprModifierPragma.make(
				TagConstants.MODIFIES,
				nothing ? (Expr)NothingExpr.make(loc) :
					    (Expr)EverythingExpr.make(loc),
				loc,null);
	}

	public final static ExprModifierPragma ensuresFalse(int loc) {
			return ExprModifierPragma.make(
			    TagConstants.ENSURES,
			    Behavior.F,
			    loc);
	}

	public final static VarExprModifierPragma defaultSignalFalse( int loc) {
		VarExprModifierPragma v = VarExprModifierPragma.make(
			    TagConstants.SIGNALS,
			    null, // Interpreted as java.lang.Exception _
			    Behavior.F,
			    loc);
		return v;
	}

	public boolean isLightweight = true;
	public boolean isNormal = false;
	public boolean isExceptional = false;
	public boolean defaultIsModifiesNothing = false;
	public ModifierPragma openPragma = null;

	public boolean isEmpty() {
		return requires.size() == 0
			&& ensures.size() == 0
			&& diverges.size() == 0 
			&& modifies.size() == 0 
			&& when.size() == 0 
			&& extras.size() == 0 
			&& signals.size() == 0;
	}

	public ArrayList requires = new ArrayList(); // of ExprModifierPragma 
	public ArrayList ensures = new ArrayList(); // of ExprModifierPragma
	public ArrayList when = new ArrayList(); // of ExprModifierPragma
	public ArrayList diverges = new ArrayList(); // of ExprModifierPragma
	public ArrayList signals = new ArrayList(); // of VarExprModifierPragma 
	public ArrayList modifies = new ArrayList();//of CondExprModifierPragma 
	public ArrayList modelPrograms = new ArrayList(); // of ModelProgramModifierPragmas
	public ArrayList subclassingContracts = new ArrayList(); // of ModifierPragmas
	public ArrayList implications = new ArrayList();
	public ArrayList examples = new ArrayList();

	public ArrayList extras = new ArrayList(); // of ModifierPragma 

	public Behavior copy() {
		Behavior b = new Behavior();
		b.isLightweight = isLightweight;
		b.isNormal = isNormal;
		b.isExceptional = isExceptional;
		b.openPragma = openPragma;
		b.requires = new ArrayList(requires);
		// We have to make copies of the ensures pragmas because
		// if the routine result is declared non_null, then
		// the fabricated ensures clause stating this needs to be
		// duplicated so that the implication can be inserted back
		// into the pragma
		b.ensures = new ArrayList();
		Iterator i = ensures.iterator();
		while (i.hasNext()) {
		    ExprModifierPragma m = (ExprModifierPragma)(i.next());
		    ExprModifierPragma mm = 
			ExprModifierPragma.make(m.getTag(),
				m.expr,m.loc);
		    mm.errorTag = m.errorTag;
		    b.ensures.add(mm);
		}
		b.when = new ArrayList(when);
		b.diverges = new ArrayList(diverges);
		b.signals = new ArrayList(signals);
		b.modifies = new ArrayList(modifies);
		return b;
	}
	public void combine(Behavior b, ArrayList orlist) {
	    if (b == null) return;

	    // The only default that is not trivially satisfied is the
	    // default for diverges in a heavyweight spec, which is
	    // 'diverges false'.
	    // But ESC/Java also needs the modifies default which is
	    // 'modifies \everything', since otherwise it presumes 
	    // locations are not modified.

	    if (!b.isLightweight && b.diverges.size() == 0)
		b.diverges.add(ExprModifierPragma.make(
				TagConstants.DIVERGES,
				Behavior.F,Location.NULL));


	    // The requires statements combine as an OR of the groups
	    // of requires clauses; each group is an AND of its components.
	    // However, if possible, we leave the components separate.
	    // Note that an empty list of requires clauses is equivalent
	    // to TRUE.

	    // req = the composite requires for this group (in b) of annotations
	    ExprModifierPragma reqclause = and(b.requires);
	    boolean reqIsTrue = reqclause == null || isTrue(reqclause.expr);
	    boolean reqIsFalse = reqclause != null && isFalse(reqclause.expr);
	    Expr reqexpr = reqclause==null? null : reqclause.expr;

	    // If the composite requires from the argument(b) are
	    // literally false, then none of the subsequent clauses are
	    // useful.  To save work, we omit them entirely.
	    if (reqIsFalse) {
		// However, we do have to add an explicitly false requires
		// clause so that we can retain the location information
		ArrayList a = new ArrayList();
		a.add(reqclause);
		orlist.add(a);
		return;
	    }

	    // Form the composite requires clause for all the groups
	    // If there is only one non-false group, then we retain the
	    // ArrayList of requires clauses from that group, so that the
	    // location information about unsatisfied requirements is as
	    // useful as possible to the user.  If there is more than one
	    // non-false group, then the groups have to be combined into
	    // a single requires annotation containing a disjunction of the
	    // conjunctions resulting from each group.

	    // b.requires is not null, but it might be empty; if it is empty
	    // it effectively means a true precondition for that group,
	    // which means that the result of the OR will be true
	    orlist.add(b.requires); 
				// orlist is an ArrayList of ArrayList of
					// ExprModifierPragma objects

	    Expr req = Behavior.T;
	    if (reqexpr != null) {
		ExprVec arg = ExprVec.make(new Expr[]{reqexpr});
		req = NaryExpr.make(Location.NULL,
				    reqexpr.getStartLoc(),TagConstants.PRE,
				    Identifier.intern("\\old"),arg);
		javafe.tc.FlowInsensitiveChecks.setType(req,
				    Types.booleanType);
	    }

	    // Add in all the annotations from the argument, taking care
	    // to guard them with the precondition

	    if (b.modifies.size() == 0) {
		b.modifies.add(Behavior.defaultModifies(Location.NULL,
					b.defaultIsModifiesNothing));
	    }
	    Iterator i = b.modifies.iterator();
	    while (i.hasNext()) {
		CondExprModifierPragma m = (CondExprModifierPragma)i.next();
		m.cond = and(m.cond,req);
		modifies.add(m);
	    }
	    i = b.ensures.iterator();
	    while (i.hasNext()) {
		ExprModifierPragma m = (ExprModifierPragma)i.next();
		if (!reqIsTrue) m.expr = implies(req,m.expr);
		if (isFalse(m.expr)) { ensures.clear(); }
		ensures.add(m);
	    }
	    i = b.when.iterator();
	    while (i.hasNext()) {
		ExprModifierPragma m = (ExprModifierPragma)i.next();
		if (!reqIsTrue) m.expr = implies(req,m.expr);
		if (isFalse(m.expr)) { when.clear(); }
		when.add(m);
	    }
	    i = b.diverges.iterator();
	    while (i.hasNext()) {
		ExprModifierPragma m = (ExprModifierPragma)i.next();
		m.expr = implies(req,m.expr);
		if (isFalse(m.expr)) { diverges.clear(); }
		diverges.add(m);
	    }
	    i = b.signals.iterator();
	    while (i.hasNext()) {
		VarExprModifierPragma m = (VarExprModifierPragma)i.next();
		if (!reqIsTrue) m.expr = implies(req,m.expr);
		signals.add(m);
	    }
	    extras.addAll(b.extras);
	}

	public void print() {
	    // FIXME - expand to print all of the fields
	    Iterator i = ensures.iterator();
	    while (i.hasNext()) {
		ExprModifierPragma m = (ExprModifierPragma)i.next();
		printSpec(m);
	    }
	}
    }
    static public class CheckPurity {

	public void visitNode(ASTNode x) {
	    if (x == null) return;
	    switch (x.getTag()) {
		case TagConstants.METHODINVOCATION:
		    MethodInvocation m = (MethodInvocation)x;
		    if (Main.options().checkPurity &&
		        !escjava.tc.FlowInsensitiveChecks.isPure(m.decl)) {
			ErrorSet.error(m.locId,
			    "Method " + m.id + " is used in an annotation" +
			    " but is not pure (" + 
			    Location.toFileLineString(m.decl.loc) + ")");
		    }
		    break;
		case TagConstants.NEWINSTANCEEXPR:
		    NewInstanceExpr c = (NewInstanceExpr)x;
		    if (Main.options().checkPurity &&
		        !escjava.tc.FlowInsensitiveChecks.isPure(c.decl)) {
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
	    }
	    {
		    int n = x.childCount();
		    for (int i = 0; i < n; ++i) {
			if (x.childAt(i) instanceof ASTNode)
				visitNode((ASTNode)x.childAt(i));
		    }
	    }
	}

    }


	// FIXME - This functionality is duplicated elsewhere, e.g. in
	// translate/GetSpec.  Should be unified and cleaned up in a common
	// utility.
    public static ModifierPragma findModifierPragma(ModifierPragmaVec v, int tag) {
	if (v == null) return null;
	for (int i=0; i<v.size(); ++i) {
		if (v.elementAt(i).getTag() == tag) return v.elementAt(i);
	}
	return null;
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
}
		




