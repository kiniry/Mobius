// This class is generated as part os the 2003 Revision of the ESC Tools
// Author: David Cok


package escjava;

import javafe.ast.*;
import javafe.util.ErrorSet;
import javafe.util.Location;
import escjava.ast.*;
import escjava.ast.TagConstants;
import escjava.ast.Modifiers;
import javafe.tc.FlowInsensitiveChecks;
import javafe.tc.Types;

import java.util.ArrayList;
import java.util.Iterator;

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
	if (pmodifiers == null) return;
	for (int i = 0; i<pmodifiers.size(); ++i) {
	    ModifierPragma mp = pmodifiers.elementAt(i);

/*
	    System.out.print("   pmod " + escjava.ast.TagConstants.toString(mp.getTag()) + " "  );
	    if (mp instanceof ExprModifierPragma) {
		ExprModifierPragma mpe = (ExprModifierPragma)mp;
		PrettyPrint.inst.print(System.out,0,mpe.expr);
	    }
	    System.out.println("");
*/

	    (new CheckPurity()).visitNode((ASTNode)mp);
/*
	    Object o;
	    if (mp instanceof ExprModifierPragma)
	      (new CheckPurity()).visitNode(((ExprModifierPragma)mp).expr);
	    if (mp instanceof CondExprModifierPragma) {
	      (new CheckPurity()).visitNode(((CondExprModifierPragma)mp).expr);
	      (new CheckPurity()).visitNode(((CondExprModifierPragma)mp).cond);
	    }
*/
	}
	Identifier id =
		tde instanceof MethodDecl ?
			((MethodDecl)tde).id
		: tde.getParent().id;
	//System.out.println("Desugaring specifications for " + id);
	tde.pmodifiers = desugarAnnotations(pmodifiers,tde);
	//if (tde.pmodifiers != pmodifiers) return;



// FIXME - control this with an option
	if (false) {
	  System.out.println("Desugared specifications for " + id);
	  for (int i = 0; i<tde.pmodifiers.size(); ++i) {
	    ModifierPragma mp = tde.pmodifiers.elementAt(i);
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
		System.out.print(((TypeName)mpe.arg.type).name.printName() + 
			" ## " + mpe.arg.id + " : ");
		print(mpe.expr);
	    }
	    System.out.println("");
	  }
        }
    }

// FIXME - this only handles one level of nesting

    protected ModifierPragmaVec desugarAnnotations(ModifierPragmaVec pm,
						RoutineDecl tde) {
	java.util.ArrayList newpm = new java.util.ArrayList();
	int size = pm.size();
	if (size == 0) return pm;
	int n = 0;
	// FIXME - check whether we should have an initial also or not ???
	// check for an initial also
	ModifierPragma m = pm.elementAt(n);
	if (m.getTag() == TagConstants.ALSO) {
	    newpm.add(m);
	    ++n;
	}
	boolean isPure = Modifiers.isPure(tde.modifiers) || 
		         Modifiers.isPure(tde.getParent().modifiers);
	// check whether this is lightweight or heavyweight
	// it is heavyweight if there is an also, a behavior annotation
	// or a OPENPRAGMA
// FIXME ?? - does an initial also require a heavyweight annotation
// DOes it matter whether it is refined or is inherited
	boolean isHeavyweight = false;
	for (int j=n; j<size; ++j) {
	    m = pm.elementAt(j);
	    int t = m.getTag();
	    if (t == TagConstants.BEHAVIOR
	     || t == TagConstants.NORMAL_BEHAVIOR
	     || t == TagConstants.EXCEPTIONAL_BEHAVIOR
	     || t == TagConstants.ALSO
	     || t == TagConstants.IMPLIES_THAT
	     || t == TagConstants.OPENPRAGMA) {
		isHeavyweight = true;
		break;
	    }
	}
	if (!isHeavyweight) return pm;

	java.util.Stack behaviors = new java.util.Stack();
	Behavior accumulatedBehavior = new Behavior();
	Behavior currentBehavior = new Behavior();
	Behavior commonBehavior = null;
	ModifierPragma openPragma = null;
	whileloop:
	while (n < size) {
	    m = pm.elementAt(n++);
	    int t = m.getTag();
	    switch (t) {
		case TagConstants.BEHAVIOR:
		    currentBehavior = new Behavior();
		    break;
		case TagConstants.NORMAL_BEHAVIOR:
		    currentBehavior = new Behavior();
		    currentBehavior.isNormal = true;
		// set a false signals clause
			// FIXME - we need to turn signals off
		    //currentBehavior.signals.add(Behavior.DefaultSignalFalse);
		    break;
		case TagConstants.EXCEPTIONAL_BEHAVIOR:
		    currentBehavior = new Behavior();
		    currentBehavior.isExceptional = true;
		    // set a false ensures clause
		    currentBehavior.ensures.add(Behavior.EnsuresFalse);
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
		    ExprModifierPragma e = (ExprModifierPragma)m;
		    currentBehavior.requires =
			and(currentBehavior.requires,e.expr);
		    break;
		}
		    
		case TagConstants.ENSURES:
		case TagConstants.ALSO_ENSURES:
		case TagConstants.POSTCONDITION: {
		    if (currentBehavior.isExceptional) {
			ErrorSet.error(m.getStartLoc(),
			   "This type of annotation is not permitted in an excpetional_behavior clause");
		    }
		    ExprModifierPragma e = (ExprModifierPragma)m;
		    currentBehavior.ensures.add(e);
		    break;
		 }

		case TagConstants.DIVERGES:
		    ExprModifierPragma e = (ExprModifierPragma)m;
		    currentBehavior.diverges.add(e);
		    break;

		case TagConstants.EXSURES:
		case TagConstants.ALSO_EXSURES:
		case TagConstants.SIGNALS:
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
		    currentBehavior.modifies.add(m);
		    if (isPure) {
			ErrorSet.error(m.getStartLoc(),
			    "A pure method may not have an assignable clause");
		    }
		    break;
		}

		case TagConstants.WHEN:
		    currentBehavior.when.add(m);
		    break;

		case TagConstants.MEASURED_BY:
		    currentBehavior.measuredby.add(m);
		    break;

		case TagConstants.OPENPRAGMA:
		    commonBehavior = currentBehavior;
		    currentBehavior = new Behavior();
		    openPragma = m;
		    break;

		case TagConstants.ALSO:
		    if (commonBehavior == null) {
			accumulatedBehavior.combine(currentBehavior);
			currentBehavior = new Behavior();
		    } else {
			currentBehavior.merge(commonBehavior);
			accumulatedBehavior.combine(currentBehavior);
			currentBehavior = new Behavior();
		    }
		    break;

		case TagConstants.CLOSEPRAGMA:
		    if (commonBehavior == null) {
			ErrorSet.error(m.getStartLoc(),
			    "Encountered |} without a matching {|");
		    } else {
			currentBehavior.merge(commonBehavior);
			accumulatedBehavior.combine(currentBehavior);
			commonBehavior = null;
			currentBehavior = null;
		    }
		    break;

		case TagConstants.IMPLIES_THAT:
		case TagConstants.EXAMPLE:
		case TagConstants.NORMAL_EXAMPLE:
		case TagConstants.EXCEPTIONAL_EXAMPLE:
			// FIXME _ for now count this as the end of annotations
			currentBehavior = null;
			break whileloop;

		case TagConstants.FOR_EXAMPLE:
			// FIXME _ for now count this as the end of annotations
			break whileloop;

		case TagConstants.PURE:
			// ignore these
			break;

	        default:
		    ErrorSet.warning(m.getStartLoc(),
			"Desugaring does not support "
			+ TagConstants.toString(m.getTag()));
		    currentBehavior.extras.add(m);
		    break;
            }
        }
	// End
	if (commonBehavior != null) {
	    ErrorSet.error(openPragma.getStartLoc(),"No closing |} for this {|");
	}
	if (currentBehavior != null && currentBehavior.isEmpty()) {
	    ErrorSet.error(m.getStartLoc(),"Dangling also");
	}

	if (currentBehavior != null && !currentBehavior.isEmpty())
		accumulatedBehavior.combine(currentBehavior);

// FIXME - what to do about locations here ?
	if (accumulatedBehavior.requires != null)
	    newpm.add(ExprModifierPragma.make(TagConstants.REQUIRES,
				accumulatedBehavior.requires,Location.NULL));
	Iterator ii = accumulatedBehavior.ensures.iterator();
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
	ii = accumulatedBehavior.measuredby.iterator();
	while (ii.hasNext()) {
	    CondExprModifierPragma e = (CondExprModifierPragma)ii.next();
	    newpm.add(e);
	}
	ii = accumulatedBehavior.modifies.iterator();
	while (ii.hasNext()) {
	    CondExprModifierPragma e = (CondExprModifierPragma)ii.next();
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

    static public Expr and(Expr e1, Expr e2) {
	if (e1 == null || isTrue(e1)) return e2;
	if (e2 == null || isTrue(e2)) return e1;
	if (isFalse(e1) || isFalse(e2)) return Behavior.F;
	Expr e = BinaryExpr.make(TagConstants.AND,e1,e2,Location.NULL);
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return e;
    }

    static public Expr or(Expr e1, Expr e2) {
	if (e1 == null || isFalse(e1)) return e2;
	if (e2 == null || isFalse(e2)) return e1;
	if (isTrue(e1) || isTrue(e2)) return Behavior.T;
	Expr e = BinaryExpr.make(TagConstants.OR,e1,e2,Location.NULL);
	javafe.tc.FlowInsensitiveChecks.setType(e,Types.booleanType);
	return e;
    }

    static public Expr implies(Expr e1, Expr e2) {
	if (isTrue(e1)) return e2;
	if (isTrue(e2)) return e2; // Yes, e2
	if (isFalse(e1)) return Behavior.T;
	if (isFalse(e2)) return Behavior.F;
	Expr e = BinaryExpr.make(TagConstants.IMPLIES,e1,e2,Location.NULL);
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
	public final static ExprModifierPragma EnsuresFalse =
			ExprModifierPragma.make(
			    TagConstants.ENSURES,
			    Behavior.F,
			    Location.NULL);
	public final static VarExprModifierPragma DefaultSignalTrue =
			VarExprModifierPragma.make(
			    TagConstants.SIGNALS,
			    FormalParaDecl.make(0,null,Identifier.intern(""),
				TypeName.make(SimpleName.make(
					Identifier.intern("Exception"),
					Location.NULL)),
				Location.NULL),
			    Behavior.T,
			    Location.NULL);
	public final static VarExprModifierPragma DefaultSignalFalse =
			VarExprModifierPragma.make(
			    TagConstants.SIGNALS,
			    FormalParaDecl.make(0,null,Identifier.intern(""),
				TypeName.make(SimpleName.make(
					Identifier.intern("Exception"),
					Location.NULL)),
				Location.NULL),
			    Behavior.F,
			    Location.NULL);

	public boolean isNormal = false;
	public boolean isExceptional = false;

	public boolean isEmpty() {
		return requires ==  null
			&& ensures.size() == 0
			&& diverges.size() == 0 
			&& signals.size() == 0;
	}
	public void merge(Behavior b) {
		requires = b.requires;
	}

	public Expr requires = null;
	public ArrayList ensures = new ArrayList(); // of ExprModifierPragma
	public ArrayList when = new ArrayList(); // of ExprModifierPragma
	public ArrayList diverges = new ArrayList(); // of ExprModifierPragma
	public ArrayList signals = new ArrayList(); // of VarExprModifierPragma 
	public ArrayList modifies = new ArrayList();//of CondExprModifierPragma 
	public ArrayList measuredby = new ArrayList();//of CondExprModifierPragma 
	public ArrayList extras = new ArrayList(); // of ModifierPragma 

	public void combine(Behavior b) {
	    if (b == null) return;

	    // set defaults for anything that has not been set
	    if (b.requires == null) b.requires = Behavior.T;

	    if (ensures.size() == 0) 
		ensures.add(ExprModifierPragma.make(
				TagConstants.ENSURES,
				Behavior.T,Location.NULL));
	    if (when.size() == 0) 
		when.add(ExprModifierPragma.make(
				TagConstants.WHEN,
				Behavior.T,Location.NULL));
	    if (diverges.size() == 0)
		diverges.add(ExprModifierPragma.make(
				TagConstants.DIVERGES,
				Behavior.F,Location.NULL));
	// FIXME - we need a default here
	    //if (signals.size() == 0) 
	//	signals.add(Behavior.DefaultSignalTrue);
	// FIXME - this needs to be "modifies \everything;"
	// but escjava does not know how to reason about that yet
	    //if (modifies.size() == 0) 
		//modifies.add(Behavior.DefaultModifies);


	    // Add in all the annotations from the argument, taking care
	    // to guard them with the precondition
	    boolean reqIsTrue = isTrue(b.requires);
	    ExprVec arg = ExprVec.make(new Expr[]{b.requires});
	    Expr req = NaryExpr.make(Location.NULL,
				b.requires.getStartLoc(),TagConstants.PRE,
				Identifier.intern("\\old"),arg);
	    javafe.tc.FlowInsensitiveChecks.setType(req,
			javafe.tc.FlowInsensitiveChecks.getType(b.requires));
		    // FIXME - should find an efficient way to avoid replicating the method name here
	    Iterator i = b.ensures.iterator();
	    while (i.hasNext()) {
		ExprModifierPragma m = (ExprModifierPragma)i.next();
		if (!reqIsTrue) m.expr = implies(req,m.expr);
		ensures.add(m);
	    }
	    i = b.when.iterator();
	    while (i.hasNext()) {
		ExprModifierPragma m = (ExprModifierPragma)i.next();
		if (!reqIsTrue) m.expr = implies(req,m.expr);
		when.add(m);
	    }
	    i = b.diverges.iterator();
	    while (i.hasNext()) {
		ExprModifierPragma m = (ExprModifierPragma)i.next();
		m.expr = implies(b.requires,m.expr);
		diverges.add(m);
	    }
	    i = b.signals.iterator();
	    while (i.hasNext()) {
		VarExprModifierPragma m = (VarExprModifierPragma)i.next();
		if (!reqIsTrue) m.expr = implies(req,m.expr);
		signals.add(m);
	    }
	    i = b.measuredby.iterator();
	    while (i.hasNext()) {
		CondExprModifierPragma m = (CondExprModifierPragma)i.next();
		m.cond = and(b.requires,m.cond);
		measuredby.add(m);
	    }
	    i = b.modifies.iterator();
	    while (i.hasNext()) {
		CondExprModifierPragma m = (CondExprModifierPragma)i.next();
		m.cond = and(b.requires,m.cond);
		modifies.add(m);
	    }
	    extras.addAll(b.extras);
	    requires = or(requires,b.requires);
	}
    }
    static public class CheckPurity {

	public void visitNode(ASTNode x) {
	    if (x == null) return;
	    switch (x.getTag()) {
		case TagConstants.METHODINVOCATION:
		    MethodInvocation m = (MethodInvocation)x;
		    if (!Modifiers.isPure(m.decl.modifiers) &&
			!Modifiers.isPure(m.decl.getParent().modifiers)) {
			ErrorSet.error(m.locId,
			    "Method " + m.id + " is used in an annotation" +
			    " but is not pure (" + 
			    Location.toFileLineString(m.decl.loc) + ")");
		    }
		    break;
		case TagConstants.NEWINSTANCEEXPR:
		    NewInstanceExpr c = (NewInstanceExpr)x;
		    if (!Modifiers.isPure(c.decl.modifiers) &&
			!Modifiers.isPure(c.decl.getParent().modifiers)) {
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

    static private void print(Expr e) {
	if (e != null) PrettyPrint.inst.print(System.out,0,e);
    }

}
		




