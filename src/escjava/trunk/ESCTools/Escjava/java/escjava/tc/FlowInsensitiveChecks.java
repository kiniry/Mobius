/* Copyright 2000, 2001, Compaq Computer Corporation */

package escjava.tc;

import java.util.Enumeration;

import javafe.ast.*;

import javafe.tc.Env;
import javafe.tc.EnvForLocals;
import javafe.tc.EnvForTypeSig;
import javafe.tc.LookupException;
import javafe.tc.TypeSig;

import javafe.util.*;

import escjava.ast.*;
import escjava.ast.Modifiers;
import escjava.ast.TagConstants;
import escjava.tc.Types;
import escjava.translate.GetSpec;  // for "findModifierPragma" -- it would be
                                   // nicer to move that method to some
                                   // utilities class somewhere
import escjava.Main;

public class FlowInsensitiveChecks extends javafe.tc.FlowInsensitiveChecks
{
    // Setup for ghost variables

    /**
     * Are we in the middle of processing an annotation? (Used by {@link GhostEnv}.)
     */
    public static boolean inAnnotation = false;
    public static boolean inModelBody = false;
	// FIXME - the above two variables are a hack!  Note that below we
	// have to save and restore their values so that the appropriate
	// values are read out of these global-static variables by GhostEnv.
	// It would be much better to create a sub Env that understands what
	// to do and pass that along for the checks. -- DRCok

    public escjava.AnnotationHandler annotationHandler = new escjava.AnnotationHandler();
    /**
     * Indicates whether <code>LS</code> is allowed in this context.  The default is
     * <code>true</code>.  For contexts where <code>LS</code> is not allowed,
     * <code>isLocksetContext</code> should be set <code>false</code> only
     * temporarily.
     */
    protected boolean isLocksetContext = true;

    /**
     * <code>\result</code> is allowed in this context when <code>isRESContext</code>
     * is <code>true</code> and <code>returnType != null</code>.  The default value
     * of <code>isRESContext</code> is <code>false</code>.  For contexts where
     * <code>isRESContext</code> should be <code>true</code>,
     * <code>isRESContext</code> should be set to <code>true</code> only temporarily.
     */
    protected boolean isRESContext = false;

    /**
     * Indicates whether <code>\old</code> and <code>\fresh</code> are allowed in
     * this context.  The default is <code>false</code>.  For contexts where these
     * functions are allowed, <code>isTwoStateContext</code> should be set
     * <code>true</code> only temporarily.
     */
    protected boolean isTwoStateContext = false;

    /**
     * Indicates whether checking is currently being done inside a <code>PRE</code>.
     * This is used by the code that disallows nested <code>PRE</code> expressions.
     * Note: alternatively, one could use <code>isTwoStateContext</code> to implement
     * this functionality, but by having a separate bit, a more precise error message
     * can be produced.
     */
    protected boolean isInsidePRE = false;

    /**
     * Indicates whether a quantification or labeled predicate is allowed in this
     * context.  This boolean is used only between one call of <code>checkExpr</code>
     * to a following recursive call.
     */
    protected boolean isPredicateContext = false;

    /**
     * Indicates whether private field accesses are allowed in the current context.
     * Private field accesses are allowed everywhere, except in postconditions of
     * overridable methods.
     */
    protected boolean isPrivateFieldAccessAllowed = true;

    protected int accessibilityLowerBound = ACC_LOW_BOUND_Private;
    // Note, "ACC_LOW_BOUND_Private" would be the same as "no lower bound"
    protected static final int ACC_LOW_BOUND_Private = 0;
    protected static final int ACC_LOW_BOUND_Package = 1;
    protected static final int ACC_LOW_BOUND_Protected = 2;
    protected static final int ACC_LOW_BOUND_Public = 3;

    /**
     * If <code>accessibilityLowerBound != ACC_LOW_BOUND_Private</code>, then
     * <code>accessibilityContext</code> is the field or routine whose modifier
     * pragma is being type checked.
     */
    /*@ invariant accessibilityContext == null ||
      @           accessibilityContext instanceof FieldDecl ||
      @           accessibilityContext instanceof RoutineDecl;
     */
    //@ readable_if accessibilityLowerBound != ACC_LOW_BOUND_Private;
    protected ASTNode accessibilityContext;

    /**
     * Acts as a parameter to <code>checkExpr</code>.  Its value is meaningful only
     * on entry to <code>checkExpr</code>.  It indicates whether the expression to be
     * checked is in a specification designator context.  In particular, this
     * parameter is used to disallow array index wild cards in non-spec designator
     * contexts.
     */
    protected boolean isSpecDesignatorContext = false;
  
    /**
     * Contains the loop invariant statement pragmas seen so far and not yet
     * processed.
     */
    protected ExprStmtPragmaVec loopInvariants = ExprStmtPragmaVec.make();

    /**
     * Contains the loop decreases statement pragmas seen so far and not yet
     * processed.
     */
    protected ExprStmtPragmaVec loopDecreases = ExprStmtPragmaVec.make();

    protected ExprStmtPragmaVec loopPredicates = ExprStmtPragmaVec.make();

    protected LocalVarDeclVec skolemConstants = LocalVarDeclVec.make();

    /**
     * Indicates whether we are are checking an invariant pragma.
     */
    protected boolean invariantContext = false;

    /**
     * Counts the number of accesses of free variables and fields used for checking
     * the appropriateness of invariants.
     */
    //@ readable_if invariantContext;
    protected int countFreeVarsAccesses = 0 ;

    /**
     * Override so that we use {@link GhostEnv} instead of {@link EnvForTypeSig}.
     */
    protected EnvForTypeSig makeEnvForTypeSig(TypeSig s,
					      boolean staticContext) {
	return new GhostEnv(s.getEnclosingEnv(), s, staticContext);
    }
  
    // Extensions to type declaration member checkers.

    protected void checkTypeDeclElem(TypeDeclElem e) {
	boolean savedInAnnotation = inAnnotation;
	boolean savedInModelBody = inModelBody;
	if (e instanceof ConstructorDecl &&
		null != GetSpec.findModifierPragma(((ConstructorDecl)e).pmodifiers,TagConstants.MODEL)) {
		inAnnotation = true;
		inModelBody = true;
	}
	if (e instanceof MethodDecl &&
		null != GetSpec.findModifierPragma(((MethodDecl)e).pmodifiers,TagConstants.MODEL)) {
		inAnnotation = true;
		inModelBody = true;
	}
        super.checkTypeDeclElem(e);
	if (e instanceof MethodDecl || e instanceof ConstructorDecl) {
		// Desugaring presumes that typechecking has already
		// been performed
		RoutineDecl m = (RoutineDecl)e;
		annotationHandler.desugar(m); 
	}
	inAnnotation = savedInAnnotation;
	inModelBody = savedInModelBody;

	// Do a separate set of checks - purity checking
	// FIXME - perhaps these should be moved into this routine
	annotationHandler.process(e);
    
        if (e.getTag() == TagConstants.INITBLOCK) {
            InitBlock ib = (InitBlock)e;
            if (ib.pmodifiers != null) {
                for (int i = 0; i < ib.pmodifiers.size(); i++) {
                    ModifierPragma mp = (ModifierPragma)ib.pmodifiers.elementAt(i);
                    ErrorSet.error(mp.getStartLoc(),
			   TagConstants.toString(mp.getTag()) +
			   " pragma cannot be applied to initializer block");
                }
            }
        }
    }

    // Extensions to Expr and Stmt checkers.

    protected Env checkStmt(Env env, Stmt s) {
        int tag = s.getTag();

        // Check for any loop invariants, loop bounds, loop predicates, or skolem
        // constants in the wrong place
        if (loopInvariants.size() != 0 || 
            loopDecreases.size() != 0 || 
            loopPredicates.size() != 0 || 
            skolemConstants.size() != 0) {
            switch (tag) {
                case TagConstants.DOSTMT: 
                case TagConstants.WHILESTMT:
                case TagConstants.FORSTMT:
                case TagConstants.LABELSTMT:
                case TagConstants.LOOP_INVARIANT:
                case TagConstants.MAINTAINING:
                case TagConstants.DECREASES:
                case TagConstants.DECREASING:
                case TagConstants.LOOP_PREDICATE:
                case TagConstants.SKOLEMCONSTANTPRAGMA:
                    break;
                default:
                    checkLoopInvariants(env, false);
                    checkLoopDecreases(env, false);
                    checkLoopPredicates(env, false);
                    checkSkolemConstants(env, false);
                    break;
            }
        }

        switch(tag) {
            case TagConstants.DOSTMT: 
            case TagConstants.WHILESTMT: {
                checkLoopInvariants(env, true);
                checkLoopDecreases(env, true);
                Env newEnv = checkSkolemConstants(env, true);
                checkLoopPredicates(newEnv, true);
                super.checkStmt(env, s);
                break;
            }
            case TagConstants.FORSTMT: {
                ForStmt f = (ForStmt)s;

                ExprStmtPragmaVec invs = loopInvariants;
                ExprStmtPragmaVec decrs = loopDecreases;
                ExprStmtPragmaVec preds = loopPredicates;
                LocalVarDeclVec skolemConsts = skolemConstants;

                loopInvariants = ExprStmtPragmaVec.make();
                loopDecreases = ExprStmtPragmaVec.make();
                loopPredicates = ExprStmtPragmaVec.make();
                skolemConstants = LocalVarDeclVec.make();

                Env se = checkStmtVec(env, f.forInit);

                Assert.notFalse(loopInvariants.size() == 0);
                Assert.notFalse(loopDecreases.size() == 0);
                Assert.notFalse(loopPredicates.size() == 0);
                Assert.notFalse(skolemConstants.size() == 0);

                loopInvariants = invs;
                loopDecreases = decrs;
                loopPredicates = preds;
                skolemConstants = skolemConsts;

                checkLoopInvariants(se, true);
                checkLoopDecreases(se, true);
                Env newEnv = checkSkolemConstants(se, true);
                checkLoopPredicates(newEnv, true);
                checkForLoopAfterInit(se, f);
                break;
            }
            case TagConstants.BLOCKSTMT: {
                env = super.checkStmt(env, s);
                // Check for any loop_invariant statement pragmas at the end of the
                // body.
                checkLoopInvariants(env, false);
                checkLoopDecreases(env, false);
                checkLoopPredicates(env, false);
                checkSkolemConstants(env, false);
                break;
            }
	    case TagConstants.VARDECLSTMT: {
		VarDeclStmt vs = (VarDeclStmt)s;
		LocalVarDecl x = vs.decl;
		if (escjava.translate.GetSpec.findModifierPragma(x.pmodifiers,
				TagConstants.GHOST) != null) {
		    boolean savedInAnnotation = inAnnotation;
		    inAnnotation = true;
		    checkTypeModifiers(env, x.type);
		    javafe.tc.PrepTypeDeclaration.inst.
			checkModifiers(x.modifiers, Modifiers.ACC_FINAL,
			    x.locId, "local ghost variable");
		    checkModifierPragmaVec(x.pmodifiers, x, env);

		    Env newEnv = new EnvForGhostLocals(env,x);
		    if (x.init != null)
			x.init = checkInit(newEnv, x.init, x.type);
		    env = newEnv;
		    inAnnotation = savedInAnnotation;
		    break;
		}

		env = super.checkStmt(env, s);
                break;

	    }
            default:
                env = super.checkStmt(env, s);
                break;
        }

        return env;
    }

    protected void checkLoopInvariants(Env env, boolean allowed) {
        for (int i = 0; i < loopInvariants.size(); i++) {
            ExprStmtPragma s = loopInvariants.elementAt(i);
            Assert.notFalse(s.getTag() == TagConstants.LOOP_INVARIANT
                            || s.getTag() == TagConstants.MAINTAINING);
            if (allowed) {
                Assert.notFalse(!isTwoStateContext);
                Assert.notFalse(!inAnnotation);
		boolean savedInAnnotation = inAnnotation;
                inAnnotation = true;
                isTwoStateContext = true;
                s.expr = checkPredicate(env, s.expr);
                inAnnotation = savedInAnnotation;
                isTwoStateContext = false;
            } else {
                errorExpectingLoop(s.getStartLoc(), TagConstants.LOOP_INVARIANT);
            }
        }
        loopInvariants.removeAllElements();
    }

    protected void checkLoopDecreases(Env env, boolean allowed) {
        for (int i = 0; i < loopDecreases.size(); i++) {
            ExprStmtPragma s = loopDecreases.elementAt(i);
            Assert.notFalse(s.getTag() == TagConstants.DECREASES
                            || s.getTag() == TagConstants.DECREASING);
            if (allowed) {
                Assert.notFalse(!isTwoStateContext);
                Assert.notFalse(!inAnnotation);
		boolean savedInAnnotation = inAnnotation;
                inAnnotation = true;
                s.expr = checkExpr(env, s.expr, Types.intType);
                inAnnotation = savedInAnnotation;
            } else {
                errorExpectingLoop(s.getStartLoc(), TagConstants.DECREASES);
            }
        }
        loopDecreases.removeAllElements();
    }

    protected void checkLoopPredicates(Env env, boolean allowed) {
        for (int i = 0; i < loopPredicates.size(); i++) {
            ExprStmtPragma s = loopPredicates.elementAt(i);
            Assert.notFalse(s.getTag() == TagConstants.LOOP_PREDICATE);
            if (allowed) {
                Assert.notFalse(!isTwoStateContext);
                Assert.notFalse(!inAnnotation);
		boolean savedInAnnotation = inAnnotation;
                inAnnotation = true;
                isTwoStateContext = true;
                s.expr = checkPredicate(env, s.expr);
                inAnnotation = savedInAnnotation;
                isTwoStateContext = false;
            } else {
                errorExpectingLoop(s.getStartLoc(), TagConstants.LOOP_PREDICATE);
            }
        }
        loopPredicates.removeAllElements();
    }

    protected Env checkSkolemConstants(Env env, boolean allowed) {
        for (int i = 0; i < skolemConstants.size(); i++) {
            LocalVarDecl s = skolemConstants.elementAt(i);
            if (allowed) {
                Assert.notFalse(!isTwoStateContext);
                Assert.notFalse(!inAnnotation);
		boolean savedInAnnotation = inAnnotation;
                inAnnotation = true;
                isTwoStateContext = true;
                env.resolveType(s.type);
                env = new EnvForLocals(env, s);
                inAnnotation = savedInAnnotation;
                isTwoStateContext = false;	
            } else {
                errorExpectingLoop(s.getStartLoc(), TagConstants.SKOLEM_CONSTANT);
            }
        }
        skolemConstants.removeAllElements();
        return env;
    }

    private void errorExpectingLoop(int loc, int tag) {
        ErrorSet.error(loc, "'" + TagConstants.toString(tag) +
                       "' pragmas can occur " +
                       "only immediately prior to a loop statement.  Loop " +
                       "statement expected (and not found) here.");
    }

    /**
     * Not to be used as a recursive call from <code>checkExpr</code>, since
     * <code>isPredicateContext</code> is set to <code>true</code>.
     */
  
    protected Expr checkPredicate(Env env, Expr e) {
        Assert.notFalse(!isPredicateContext);
        isPredicateContext = true;
        Expr ee = checkExpr(env, e, Types.booleanType);
        // "isPredicateContext" is reset by "checkExpr"
        Assert.notFalse(!isPredicateContext);
        return ee;
    }

    //@ also_ensures !isPredicateContext
    protected Expr checkExpr(Env env, Expr e) {
        // Anticipate that the next context is probably not one suitable for
        // quantifications and labels.  "isPredicateContext" must revert to its old
        // value before return.
        boolean isCurrentlyPredicateContext = isPredicateContext;
        isPredicateContext = false;

        if (getTypeOrNull(e) != null )
            // already done
            return e;

        // No recursive call to "checkExpr" is a specification designator context, so
        // set "isSpecDesignatorContext" to "false", keeping the initial value in
        // local variable "isCurrentlySpecDesignatorContext".
        boolean isCurrentlySpecDesignatorContext = isSpecDesignatorContext;
        isSpecDesignatorContext = false;
    
        int tag = e.getTag();
        switch(tag) {

            // Handle accesses to ghost fields as well...
            case TagConstants.FIELDACCESS:
                {
                    if (!inAnnotation)
                        return super.checkExpr(env, e);
	
                    // a field access is considerded a free variable access in an
                    // invariant.
                    if (invariantContext) countFreeVarsAccesses++;

                    // set default result type to errorType, in case there is an error.
                    setType( e, Types.errorType );
                    FieldAccess fa = (FieldAccess)e;
                    Type t = checkObjectDesignator(env, fa.od);
                    if (t==null)
                        return fa;
                    if (t instanceof TypeName)
                        t = TypeSig.getSig( (TypeName) t );

                    try {
                        fa.decl = escjava.tc.Types.lookupField( t, fa.id, sig );
                    } catch( LookupException ex) {
                        reportLookupException(ex, "field", Types.printName(t), fa.locId);
                        return fa;
                    }
                    setType( fa, fa.decl.type );

                    if (fa.od instanceof TypeObjectDesignator &&
			!GhostEnv.isStatic(fa.decl)) {
                        // Is fa.decl an instance field of the same class as fa is
                        // part of?
                        boolean thisField = false;
                        if (fa.decl.parent != null)
                            thisField = (env.getEnclosingClass()
                                         .isSubtypeOf(TypeSig.getSig(fa.decl.parent)));
	    
                        if (thisField ||
                            ((TypeObjectDesignator)fa.od).type instanceof TypeName) {

                            ErrorSet.error(fa.locId,
                                           "An instance field may be accessed only via "
                                           + "an object and/or from a non-static"
                                           + " context or an inner class enclosed"
                                           + " by a type possessing that field.");

                        } else
                            ErrorSet.error(fa.locId,
                                           "The instance fields of type "
                                           + ((TypeObjectDesignator)fa.od).type
                                           + " may not be accessed from type "
                                           + sig);
                    }

                    if (!isPrivateFieldAccessAllowed &&
                        Modifiers.isPrivate(fa.decl.modifiers) &&
                        GetSpec.findModifierPragma(fa.decl,
			       TagConstants.SPEC_PUBLIC) == null &&
                        GetSpec.findModifierPragma(fa.decl,
			       TagConstants.SPEC_PROTECTED) == null) {
                        ErrorSet.error(fa.locId, 
			   "A private field can be used in "+
			   "postconditions of overridable methods only if "+
			   "it is declared spec_public or spec_protected");
                    }

                    // The following code checks that "fa" is at least as
                    // spec-accessible as "accessibilityContext" is Java-accessible.
                    // This is vacuously true if "accessibilityLowerBound" is
                    // private.
                    if (accessibilityLowerBound != ACC_LOW_BOUND_Private) {
                        boolean isAccessibleEnough;
                        if (Modifiers.isPublic(fa.decl.modifiers) ||
                            GetSpec.findModifierPragma(fa.decl,
                                                       TagConstants.SPEC_PUBLIC) != null) {
                            // public and spec_public fields are always accessible
                            isAccessibleEnough = true;
	    
                        } else if (Modifiers.isPrivate(fa.decl.modifiers)) {
                            // Note: if "fa" type-checked so far, then "fa.decl" and
                            // "accessibilityContext" are declared in the same class.
                            // It would be nice to assert this fact at run-time, but
                            // control may reach this point even if "fa" does not
                            // type-check above.

                            // "fa.decl" can be private only if
                            // "accessibilityContext" is private, which was checked
                            // above
                            isAccessibleEnough = false;
	    
                        } else if (Modifiers.isPackage(fa.decl.modifiers)) {
                            // Note: if "fa" type-checked so far, then "fa.decl" and
                            // "accessibilityContext" are declared in the same
                            // package.  It would be nice to assert this fact at
                            // run-time, but control may reach this point even if
                            // "fa" does not type-check above.

                            // "fa.decl" can be package (default) accessible only if
                            // "accessibilityContext" is private (which was checked
                            // above) or package
                            isAccessibleEnough =
                                (accessibilityLowerBound == ACC_LOW_BOUND_Package);
	    
                        } else {
                            Assert.notFalse(Modifiers.isProtected(fa.decl.modifiers));
                            // Note: if "fa" type-checked so far, then either
                            // "fa.decl" and "accessibilityContext" are declared in
                            // the same package or the class declaring
                            // "accessibilityContext" is a subtype of the class
                            // declaring "fa.decl".  It would be nice to assert this
                            // fact at run-time, but control may reach this point
                            // even if "fa" does not type-check above.

                            // "fa.decl" can be protected only if
                            // "accessibilityContext" is private (which was checked
                            // above) or package, or if "accessibilityContext" is
                            // protected and "fa.decl" is declared in a superclass of
                            // the class that declares "accessibilityContext".
                            isAccessibleEnough = false;
                            if (accessibilityLowerBound == ACC_LOW_BOUND_Package) {
                                isAccessibleEnough = true;
                            } else if (accessibilityLowerBound == ACC_LOW_BOUND_Protected) {
                                TypeDecl tdContext;
                                if (accessibilityContext instanceof FieldDecl) {
                                    tdContext = ((FieldDecl)accessibilityContext).parent;
                                } else {
                                    tdContext = ((RoutineDecl)accessibilityContext).parent;
                                }
                                TypeSig tsContext = TypeSig.getSig(tdContext);
                                if (tsContext.isSubtypeOf(TypeSig.getSig(fa.decl.parent))) {
                                    isAccessibleEnough = true;
                                }
                            }
                        }
                        if (!isAccessibleEnough) {
                            ErrorSet.error(fa.locId, "Fields mentioned in this modifier "+
                                           "pragma must be at least as accessible "+
                                           "as the field/method being modified (perhaps "+
                                           "try spec_public)");
                        }
                    }
  
                    return fa;
                }

            case TagConstants.METHODINVOCATION:
                {
			countFreeVarsAccesses++;
/*                    if (!inAnnotation)
                        return super.checkExpr(env, e);
	
                    MethodInvocation mi = (MethodInvocation)e;
                    ErrorSet.error(mi.locId,
                                   "Specification expressions are not allowed to "+
                                   "contain method invocations");
                    setType(e, Types.voidType);
                    return e;
*/
		    return super.checkExpr(env,e);
                }
      
            case TagConstants.IMPLIES:
            case TagConstants.EXPLIES:
            case TagConstants.IFF:
            case TagConstants.NIFF:
                {
                    BinaryExpr be = (BinaryExpr)e;
                    // each argument is allowed to contain quantifiers and labels if
                    // this expression is
                    isPredicateContext = isCurrentlyPredicateContext;
                    be.left = checkExpr(env, be.left, Types.booleanType);
                    isPredicateContext = isCurrentlyPredicateContext;
                    be.right = checkExpr(env, be.right, Types.booleanType);

                    // check illegal associativity of ==> and <==
                    if ((tag == TagConstants.IMPLIES &&
                         (be.left.getTag() == TagConstants.EXPLIES ||
                          be.right.getTag() == TagConstants.EXPLIES)) ||
                        (tag == TagConstants.EXPLIES &&
                         (be.left.getTag() == TagConstants.IMPLIES ||
                          be.right.getTag() == TagConstants.IMPLIES))) {
                        // unfortunately, we don't have the location of either of the
                        // operators at fault
                        ErrorSet.error(be.getStartLoc(),
                                       "Ambiguous association of ==> and <==.  " +
                                       "Use parentheses to disambiguate.");
                    }

                    setType(e, Types.booleanType);
                    return e;
                }

            case TagConstants.DOTDOT:
		{
                    BinaryExpr be = (BinaryExpr)e;
                    // each argument is allowed to contain quantifiers and labels if
                    // this expression is
		    isPredicateContext = false;
                    be.left = checkExpr(env, be.left, Types.intType);
                    be.right = checkExpr(env, be.right, Types.intType);

// FIXME - this really needs to be a range type
                    setType(e, Types.intType);
                    return e;
                }

            case TagConstants.SUBTYPE:
                {
                    BinaryExpr be = (BinaryExpr)e;
                    Type expected = Types.booleanType;
		    if (tag == TagConstants.SUBTYPE) 
				expected = Types.typecodeType;
                    be.left = checkExpr(env, be.left, expected);
                    be.right = checkExpr(env, be.right, expected);
                    setType(e, Types.booleanType);
                    return e;
                }

            case TagConstants.FRESH:
                {
                    NaryExpr ne = (NaryExpr)e;
                    if (ne.exprs.size() != 1) {
                        ErrorSet.error(ne.sloc, 
                                       "The function fresh takes only one argument");
                    } else if (!isTwoStateContext) {
                        ErrorSet.error(ne.sloc, 
                                       "The function \\fresh cannot be used in this context");
                    } else if (isInsidePRE) {
                        ErrorSet.error(ne.sloc, "The function \\fresh cannot be used "+
                                       "inside a \\old expression");
                    } else {
                        Expr nu = 
                            checkExpr(env, ne.exprs.elementAt(0), Types.javaLangObject());
                        ne.exprs.setElementAt(nu, 0);			
                    }
                    setType(e, Types.booleanType);
                    return e;
                }

            case TagConstants.ELEMSNONNULL:
                {
                    NaryExpr ne = (NaryExpr)e;
                    if( ne.exprs.size() != 1 ) 
                        ErrorSet.error( ne.sloc, 
                                        "The function \\nonnullelements takes only one argument");
                    else {
                        Expr nu = checkExpr(env, ne.exprs.elementAt(0),
                                            ArrayType.make(Types.javaLangObject(),
                                                           Location.NULL));
                        ne.exprs.setElementAt( nu, 0 );
                    }
                    setType( e, Types.booleanType );
                    return e;
                }

            case TagConstants.DTTFSA:
                {
                    NaryExpr ne = (NaryExpr)e;
                    Type resultType = Types.voidType;
                    if (ne.exprs.size() < 2) {
                        Assert.notFalse(1 <= ne.exprs.size());
                        ErrorSet.error(ne.sloc, 
                                       "The function \\dttfsa requires at least two arguments");
                    } else {
                        // type check each of the arguments
                        for (int i = 0; i < ne.exprs.size(); i++) {
                            Expr nu = checkExpr(env, ne.exprs.elementAt(i));
                            ne.exprs.setElementAt(nu, i);
                        }
                        // the first argument should be a TypeExpr; retrieve the type
                        // it denotes
                        resultType = ((TypeExpr)ne.exprs.elementAt(0)).type;
                        // the second argument should be a String literal
                        Expr arg1 = ne.exprs.elementAt(1);
                        if (arg1.getTag() != TagConstants.STRINGLIT) {
                            ErrorSet.error(arg1.getStartLoc(),
                                           "The second argument to \\dttfsa must be a String literal");
                        } else {
                            LiteralExpr lit = (LiteralExpr)arg1;
                            String op = (String)lit.value;
                            if (op.equals("identity") && ne.exprs.size() != 3) {
                                ErrorSet.error(ne.sloc, 
                                               "The function \\dttfsa requires exactly 3 arguments when the second argument is \"identity\"");
                            }
                        }
                    }
                    setType(e, resultType);
                    return e;
                }
/*
	    case TagConstants.WACK_NOWARN:
	    case TagConstants.NOWARN_OP:
	    case TagConstants.WARN:
	    case TagConstants.WARN_OP:
	        {
                    NaryExpr ne = (NaryExpr)e;
		    Expr nu;
                    if( ne.exprs.size() != 1 ) {
                        ErrorSet.error(ne.sloc, 
                                       "The function " + TagConstants.toString(tag) + 
                                       " takes only one argument");
			setType( e, Types.errorType );
                    } else {
                        nu = checkExpr(env, ne.exprs.elementAt(0));
                        ne.exprs.setElementAt( nu, 0 );			
			setType( e, getType(nu) );
                    }
                    return e;
                }
*/
            case TagConstants.ELEMTYPE:
                {
                    NaryExpr ne = (NaryExpr)e;
                    if( ne.exprs.size() != 1 ) 
                        ErrorSet.error(ne.sloc, 
                                       "The function \\elemtype takes only one argument");
                    else {
                        Expr nu = checkExpr(env, ne.exprs.elementAt(0));
                        ne.exprs.setElementAt( nu, 0 );			
			if (!Types.isTypeType(getType(nu)))
			    ErrorSet.error(nu.getStartLoc(),
				"The argument must have TYPE type");
                    }
                    setType( e, Types.typecodeType );
                    return e;
                }

	    case TagConstants.WACK_DURATION:
	    case TagConstants.WACK_WORKING_SPACE:
	    case TagConstants.SPACE:
		{
                    NaryExpr ne = (NaryExpr)e;
                    if( ne.exprs.size() != 1 ) 
                        ErrorSet.error(ne.sloc, 
                                       "The function " + TagConstants.toString(tag) + 
                                       " takes only one argument");
                    else {
			// Note: the arguments are not evaluated
                        Expr nu = checkExpr(env, ne.exprs.elementAt(0));
                        ne.exprs.setElementAt( nu, 0 );			
                    }
                    setType( e, Types.longType );
                    return e;
                }

            case TagConstants.NOT_MODIFIED:
                {
                    NaryExpr ne = (NaryExpr)e;
// FIXME - Is this a one argument function ?
                    if( ne.exprs.size() != 1 ) 
                        ErrorSet.error( ne.sloc, 
                                        "The function \\not_modified takes only one argument");
                    else {
                        Expr nu = checkExpr(env, ne.exprs.elementAt(0));
                        ne.exprs.setElementAt( nu, 0 );			
                    }
                    setType( e, Types.booleanType );
                    return e;
                }

            case TagConstants.MAX:
                {
                    NaryExpr ne = (NaryExpr)e;
                    if( ne.exprs.size() != 1 ) 
                        ErrorSet.error( ne.sloc, 
                                        "The function \\max takes only one argument");
                    else {
                        Expr nu = checkExpr(env, ne.exprs.elementAt(0), Types.locksetType);
                        ne.exprs.setElementAt( nu, 0 );			
                    }
                    setType( e, Types.javaLangObject() );
                    return e;
                }

            case TagConstants.PRE:
                {
                    NaryExpr ne = (NaryExpr)e;
                    if( ne.exprs.size() != 1 ) {
                        ErrorSet.error( ne.sloc, 
                                        "The function \\old takes only one argument");
                        setType(e, Types.voidType);
                    } else if (!isTwoStateContext) {
                        ErrorSet.error(ne.sloc, 
                                       "The function \\old cannot be used in this context");
                        setType(e, Types.voidType);
                    } else if (isInsidePRE) {
                        ErrorSet.error(ne.sloc, "Nested applications of \\old not allowed");
                        setType(e, Types.voidType);
                    } else {
                        isInsidePRE = true;
                        Expr nu = checkExpr(env, ne.exprs.elementAt(0) );
                        Assert.notFalse(isInsidePRE);
                        isInsidePRE = false;
                        ne.exprs.setElementAt( nu, 0 );			
                        setType( e, getType( nu ) );
                    }
                    return e;
                }

            case TagConstants.TYPEOF:
                {
                    NaryExpr ne = (NaryExpr)e;
                    if( ne.exprs.size() != 1 ) 
                        ErrorSet.error( ne.sloc, 
                                        "The function \\typeof takes only one argument");
                    else {
                        Expr nu = 
                            checkExpr(env, ne.exprs.elementAt(0), Types.javaLangObject() );
                        ne.exprs.setElementAt( nu, 0 );			
                    }
                    setType( e, Types.typecodeType );
                    return e;
                }

            case TagConstants.TYPEEXPR:
                {
                    TypeExpr te = (TypeExpr)e;
                    env.resolveType( te.type );
                    setType(e, Types.typecodeType );
                    return e;
                }

            case TagConstants.LABELEXPR:
                {
                    LabelExpr le = (LabelExpr)e;
                    if (!isCurrentlyPredicateContext) {
                        ErrorSet.error(le.getStartLoc(),
                                       "Labeled predicates are not allowed in this context");
                        setType(e, Types.booleanType);
                    } else {
                        isPredicateContext = true;
                        le.expr = checkExpr(env, le.expr);
                        setType(e, getType( le.expr ) );
                    }
                    return e;
                }

            case TagConstants.NUM_OF:
	        {
                    NumericalQuantifiedExpr qe = (NumericalQuantifiedExpr)e;
	
                    if (!isCurrentlyPredicateContext) {
                        ErrorSet.error(qe.getStartLoc(),
			   "Quantified expressions are not allowed in this context");
                    } else {
                        Env subenv = env;
	
                        for( int i=0; i<qe.vars.size(); i++) {
                            GenericVarDecl decl = qe.vars.elementAt(i);
                            env.resolveType( decl.type );
	    
                            subenv = new EnvForLocals(subenv, decl);
                        }
                        isPredicateContext = true;
                        qe.expr = checkExpr(subenv, qe.expr, Types.booleanType);
                    }
                    setType(e, Types.intType);
                    return e;
                }

            case TagConstants.SUM:
            case TagConstants.PRODUCT:
            case TagConstants.MIN:
            case TagConstants.MAXQUANT:
                {
                    GeneralizedQuantifiedExpr qe = (GeneralizedQuantifiedExpr)e;
	
                    if (!isCurrentlyPredicateContext) {
                        ErrorSet.error(qe.getStartLoc(),
			   "Quantified expressions are not allowed in this context");
                    } else {
                        Env subenv = env;
	
                        for( int i=0; i<qe.vars.size(); i++) {
                            GenericVarDecl decl = qe.vars.elementAt(i);
                            env.resolveType( decl.type );
	    
                            subenv = new EnvForLocals(subenv, decl);
                        }
                        isPredicateContext = true;
                        qe.rangeExpr = checkExpr(subenv, qe.rangeExpr, Types.booleanType);
                        qe.expr = checkExpr(subenv, qe.expr, Types.intType);
                    }
                    setType(e, Types.intType);
                    return e;
                }

	    case TagConstants.FORALL:
            case TagConstants.EXISTS:
                {
                    QuantifiedExpr qe = (QuantifiedExpr)e;
	
                    if (!isCurrentlyPredicateContext) {
                        ErrorSet.error(qe.getStartLoc(),
                                       "Quantified expressions are not allowed in this context");
                    } else {
                        Env subenv = env;
	
                        for( int i = 0; i < qe.vars.size(); i++) {
                            GenericVarDecl decl = qe.vars.elementAt(i);
                            env.resolveType(decl.type);
	    
                            subenv = new EnvForLocals(subenv, decl);
                        }
                        isPredicateContext = true;
                        qe.expr = checkExpr(subenv, qe.expr, Types.booleanType);
                    }
                    setType(e, Types.booleanType);
                    return e;
                }

            case TagConstants.PARENEXPR:
            case TagConstants.NOT:
                {
                    // the sub-expression is allowed to contain quantifiers and
                    // labels if this expression is
                    isPredicateContext = isCurrentlyPredicateContext;
                    return super.checkExpr(env, e);
                }

            case TagConstants.OR:
            case TagConstants.AND:
            case TagConstants.EQ:
            case TagConstants.NE:
                {
                    BinaryExpr be = (BinaryExpr)e;
                    // each argument is allowed to contain quantifiers and labels if
                    // this expression is
                    isPredicateContext = isCurrentlyPredicateContext;
                    be.left = checkExpr(env, be.left);
                    isPredicateContext = isCurrentlyPredicateContext;
                    be.right = checkExpr(env, be.right);
		    if (false && Types.isTypeType(getType(be.left)) &&
// DO WE NEED TO check the composite expressions ??? FIXME TYPE-EQUIV
			Types.isTypeType(getType(be.right))) {
			setType( be, Types.booleanType);
		    } else {
			Type t = checkBinaryExpr(be.op, be.left, be.right, be.locOp);
			setType( be, t );
		    }
                    return be;
                }
      
            case TagConstants.WILDREFEXPR:
                {
                    WildRefExpr r = (WildRefExpr)e;
                    if (!isCurrentlySpecDesignatorContext) {
                        setType(r, Types.intType);
                        ErrorSet.error(r.locOpenBracket,
                                       "Array index wild cards allowed only as "+
                                       "specification designators");
                    } else {
                        r.expr = checkExpr(env, r.expr);
                        Type arrType = getType( r.expr );
	
                        if( arrType instanceof ArrayType ) {
                            setType( r, ((ArrayType)arrType).elemType );
                        } else {
                            setType( r, Types.errorType );
			    if (!Types.isErrorType(arrType))
				ErrorSet.error( r.locOpenBracket, 
                                            "Attempt to index a non-array value");
                        }
                    }
                    return r;
                }      

            case TagConstants.ARRAYREFEXPR:
                {
                    ArrayRefExpr r = (ArrayRefExpr)e;
	
                    r.array = checkExpr(env, r.array);
                    Type arrType = getType( r.array );
                    r.index = checkExpr(env, r.index);
                    Type t = getType( r.index );

                    if( arrType instanceof ArrayType ) {
                        setType( r, ((ArrayType)arrType).elemType );
                        Type ndxType = 
                            Types.isNumericType( t ) ? Types.unaryPromote( t ) : t;
                        if( !Types.isSameType( ndxType, Types.intType ) ) 
                            ErrorSet.error(r.locOpenBracket, "Array index is not an integer");

                    } else if( arrType.getTag() == TagConstants.LOCKSET ) {
                        setType( r, Types.booleanType );
                        if( !Types.isReferenceOrNullType( t ) )
                            ErrorSet.error(r.locOpenBracket, 
                                           "Can only index \\lockset with a reference type");
                    } else {
                        setType( r, Types.errorType );
			if (!Types.isErrorType(arrType))
			    ErrorSet.error( r.locOpenBracket, 
                                        "Attempt to index a non-array value");
                    }

                    return r;
                }

            case TagConstants.RESEXPR:
                {
                    if (!isRESContext || returnType == null) {
                        ErrorSet.error(e.getStartLoc(), 
                                       "Keyword \\result is not allowed in this context");
                        setType( e, Types.intType );
                    }
                    else
                        setType( e, returnType );

                    return e;
                }

	    case TagConstants.SETCOMPEXPR:
		{
		    SetCompExpr s = (SetCompExpr)e;

		    env.resolveType(s.type);
		    env.resolveType(s.fp.type);
		    Env subenv = new EnvForLocals(env,s.fp);
		    boolean savedPredicateContext = isPredicateContext;
		    isPredicateContext = true;
		    s.expr = checkExpr(subenv, s.expr, Types.booleanType);
		    isPredicateContext = savedPredicateContext;
		    setType( e, s.type);
// FIXME - CHeck that the type is only JMLObjectSet, JMLValueSet
// Check that the predicate has the correct restricted form
		    return e;
		}

	    case TagConstants.NOTSPECIFIEDEXPR:
		{
		    setType( e, Types.voidType);
		    return e;
		}
	    case TagConstants.EVERYTHINGEXPR:
		{
		    if (!isCurrentlySpecDesignatorContext) {
			ErrorSet.error(e.getStartLoc(),
				"Keyword \\everything is not allowed in this context");
			setType( e, Types.errorType);
		    } else {
			setType( e, Types.voidType);
		    }
		    return e;
		}
	    case TagConstants.NOTHINGEXPR:
		{
		    if (!isCurrentlySpecDesignatorContext) {
			ErrorSet.error(e.getStartLoc(),
				"Keyword \\nothing is not allowed in this context");
			setType( e, Types.errorType);
		    } else {
			setType( e, Types.voidType);
		    }
		    return e;
		}
            case TagConstants.LOCKSETEXPR:
                {
                    if (! isLocksetContext) {
                        ErrorSet.error(e.getStartLoc(),
                                       "Keyword \\lockset is not allowed in this context");
                    }
                    setType( e, Types.locksetType );
                    return e;
                }

            case TagConstants.LE: 
            case TagConstants.LT: 
                {
                    BinaryExpr be = (BinaryExpr)e;
                    be.left = checkExpr(env, be.left);
                    be.right = checkExpr(env, be.right);
	
                    if( Types.isReferenceOrNullType( getType( be.left ) )
                        && Types.isReferenceOrNullType( getType( be.right ) ) ) {
                        // is lock comparison, and is ok
                        setType( be, Types.booleanType );
                        return be;
                    } else {
                        return super.checkExpr(env, e);
                    }
                }

            case TagConstants.NEWINSTANCEEXPR:
            case TagConstants.NEWARRAYEXPR:
                {
		    countFreeVarsAccesses++;
                    if (inAnnotation) {
/* FIXME - Yes it can, but it must be pure!
                        ErrorSet.error(e.getStartLoc(),
			   "new cannot be used in specification expressions");
*/
                    }
                    return super.checkExpr(env, e);
                }
      
            case TagConstants.ASSIGN: case TagConstants.ASGMUL:
            case TagConstants.ASGDIV: case TagConstants.ASGREM:
            case TagConstants.ASGADD: case TagConstants.ASGSUB:
            case TagConstants.ASGLSHIFT: case TagConstants.ASGRSHIFT:
            case TagConstants.ASGURSHIFT: case TagConstants.ASGBITAND:
            case TagConstants.ASGBITOR: case TagConstants.ASGBITXOR:
                {
                    if (inAnnotation && !inModelBody) {
                        BinaryExpr be = (BinaryExpr)e;
                        ErrorSet.error(be.locOp,
			   "assignments cannot be used in specification expressions");
                    }
                    return super.checkExpr(env, e);
                }
      
            case TagConstants.INC: case TagConstants.DEC: 
            case TagConstants.POSTFIXINC: case TagConstants.POSTFIXDEC:
                {
                    if (inAnnotation && !inModelBody) {
                        UnaryExpr ue = (UnaryExpr)e;
                        ErrorSet.error(ue.locOp,
			   "assignments cannot be used in specification expressions");
                    }
                    return super.checkExpr(env, e);
                }
      
            default:
                return super.checkExpr(env, e);
        }
    }

    // Pragma checkers

    protected  void checkTypeDeclElemPragma(TypeDeclElemPragma e) {
        int tag = e.getTag();
	boolean savedInAnnotation = inAnnotation;
        inAnnotation = true;	// Must be reset before we exit!

        switch(tag) {
            case TagConstants.AXIOM:
	    case TagConstants.INITIALLY:
            case TagConstants.INVARIANT:
	    case TagConstants.CONSTRAINT: // FIXME - do we need to change the logic below to handle constraints?
	    case TagConstants.REPRESENTS:
                {
                    ExprDeclPragma ep = (ExprDeclPragma)e;
                    Env rootEnv = (tag == TagConstants.AXIOM) ? rootSEnv : rootIEnv;

                    invariantContext = (tag == TagConstants.INVARIANT);
		    isTwoStateContext = (tag == TagConstants.CONSTRAINT);
                    boolean oldIsLocksetContext = isLocksetContext;
                    isLocksetContext = false;
                    if (invariantContext){
 // FIXME                       Assert.notFalse(countFreeVarsAccesses == 0);
                        countFreeVarsAccesses = 0;
                    }
	
                    ep.expr = checkPredicate(rootEnv, ep.expr);
                    isLocksetContext = oldIsLocksetContext;

                    TypeSig sig = TypeSig.getSig(e.getParent());
                    if (sig==javafe.tc.Types.javaLangObject() ||
                        sig==javafe.tc.Types.javaLangCloneable()) {
                        if (invariantContext) ErrorSet.fatal(e.getStartLoc(),
			   "java.lang.Object and java.lang.Cloneable may not"
			   + " contain invariants.");  // FIXME - Why?
                    }
                    if (invariantContext && countFreeVarsAccesses == 0 &&
			// Don't print an error if the entire invariant
			// is an informal predicate
			escjava.parser.EscPragmaParser.
			     informalPredicateDecoration.get(ep.expr)==null) {
/*
FIXME - see uses of countFreeVarsAccess
                        ErrorSet.error(e.getStartLoc(),
			   "Class invariants must mention program variables"
			   + " or fields.");
*/
                    }

                    if (invariantContext) {countFreeVarsAccesses = 0;}
                    invariantContext = false;
                    isTwoStateContext = false;
                    break;
                }

	    case TagConstants.DEPENDS:
		{
                    DependsPragma ep = (DependsPragma)e;
			// FIXME - perhaps use rootSEnv if the variable
			// being discussed is static ?
                    Env rootEnv = rootIEnv;

		    ep.target = checkExpr(rootEnv, ep.target);

		    ExprVec ev = ep.exprs;
		    for (int i=0; i<ev.size(); ++i) {
			ev.setElementAt(
				checkExpr(rootEnv, ev.elementAt(i)), i);
		    }

		// FIXME - Need to check that
		//	LHS is a simple model variable, a field of 
		//		this or a super class or an interface
		//	RHS consists of store-refs, no computed expressions
		//	RHS may have other model variables
		//	check access ?
                    break;
                }

	    case TagConstants.MODELCONSTRUCTORDECLPRAGMA: {
		ModelConstructorDeclPragma me = (ModelConstructorDeclPragma)e;
                ConstructorDecl cd = me.decl;
                Env rootEnv = Modifiers.isStatic(cd.modifiers)
                    ? rootSEnv
                    : rootIEnv;

		// All gets checked since the associated ConstructorDecl is
		// part of the type

		// FIXME - the body needs to allow ghost/model vars
		break;
            }


	    case TagConstants.MODELMETHODDECLPRAGMA: {
                MethodDecl decl = ((ModelMethodDeclPragma)e).decl;
                Env rootEnv = Modifiers.isStatic(decl.modifiers)
                    ? rootSEnv
                    : rootIEnv;

		// All gets checked since the associated ConstructorDecl is
		// part of the type

		// FIXME - the body needs to allow ghost/model vars
		break;
            }

	    case TagConstants.MODELDECLPRAGMA: {
                FieldDecl decl = ((ModelDeclPragma)e).decl;
                Env rootEnv = Modifiers.isStatic(decl.modifiers)
                    ? rootSEnv
                    : rootIEnv;

                rootEnv.resolveType( decl.type );
                checkModifierPragmaVec( decl.pmodifiers, decl, rootEnv );
		checkTypeModifiers(rootEnv, decl.type);

		// Check for both static and instance declarations

		if (Modifiers.isStatic(decl.modifiers)) {
		    ModifierPragma inst = GetSpec.findModifierPragma(decl,
					TagConstants.INSTANCE);
		    if (inst != null) ErrorSet.error(inst.getStartLoc(),
			"May not specify both static and instance on a declaration");
		}

                /*
                 * Check for other fields with the same name:
                 */
                {
		    TypeDeclElemVec elems = decl.parent.elems;
		    FieldDecl fd;
		    for (int i = 0; i<elems.size(); ++i) {
			TypeDeclElem tde = elems.elementAt(i);
			if (tde instanceof FieldDecl) {
			    fd = (FieldDecl)tde;
			} else if (tde instanceof GhostDeclPragma) {
			    fd = ((GhostDeclPragma)tde).decl;
			} else if (tde instanceof ModelDeclPragma) {
			    fd = ((ModelDeclPragma)tde).decl;
			} else
			    continue;
			if (fd.id ==  decl.id && fd != decl)
			    ErrorSet.error(decl.locId,
                                   "Another field named '"+decl.id.toString()
                                   +"' already exists in this type", fd.locId);
		    }
                }

                break;
            }

            case TagConstants.GHOSTDECLPRAGMA: {
                FieldDecl decl = ((GhostDeclPragma)e).decl;
                Env rootEnv = Modifiers.isStatic(decl.modifiers)
                    ? rootSEnv
                    : rootIEnv;

                rootEnv.resolveType( decl.type );
                checkModifierPragmaVec( decl.pmodifiers, decl, rootEnv );
		checkTypeModifiers(rootEnv, decl.type);


		// Check for both static and instance declarations

		if (Modifiers.isStatic(decl.modifiers)) {
		    ModifierPragma inst = GetSpec.findModifierPragma(decl,
					TagConstants.INSTANCE);
		    if (inst != null) ErrorSet.error(inst.getStartLoc(),
			"May not specify both static and instance on a declaration");
		}

                /*
                 * Handle initializer:
                 */

		if (decl.init != null) {
			leftToRight = true;
			allowedExceptions.removeAllElements();
			Assert.notFalse( allowedExceptions.size() == 0);
			decl.init = checkInit(rootEnv, decl.init, decl.type);
		}

                /*
                 * Check for other fields with the same name:
                 */
		{
		    TypeDeclElemVec elems = decl.parent.elems;
		    FieldDecl fd;
		    for (int i = 0; i<elems.size(); ++i) {
			TypeDeclElem tde = elems.elementAt(i);
			if (tde instanceof FieldDecl) {
			    fd = (FieldDecl)tde;
			} else if (tde instanceof GhostDeclPragma) {
			    fd = ((GhostDeclPragma)tde).decl;
			} else if (tde instanceof ModelDeclPragma) {
			    fd = ((ModelDeclPragma)tde).decl;
			} else
			    continue;
			if (fd.id ==  decl.id && fd != decl)
			    ErrorSet.error(decl.locId,
                                   "Another field named '"+decl.id.toString()
                                   +"' already exists in this type", fd.locId);
		    }
                }


                break;
            }

            case TagConstants.STILLDEFERREDDECLPRAGMA: {
                StillDeferredDeclPragma sddp = (StillDeferredDeclPragma)e;
                if (!sig.hasField(sddp.var)) {
                    ErrorSet.error(sddp.locId, "No such field");
                }

                // TBW:  To support still_deferred, one also needs to check that
                // "sddp.var" is declared as writable-deferred in the direct
                // superclass.
                break;
            }

            default:
                Assert.fail("Unexpected tag " + tag + 
				" " + TagConstants.toString(tag));
        }
        inAnnotation = savedInAnnotation;
    }

    protected Env checkModifierPragma(ModifierPragma p, ASTNode ctxt, Env env) {

	boolean savedInAnnotation = inAnnotation;
        inAnnotation = true;	// Must be reset before we exit!
        int tag = p.getTag();
        switch(tag) 
        {
	    case TagConstants.EVERYTHINGEXPR:
	    case TagConstants.EVERYTHING:
	    case TagConstants.NOTHING:
	    case TagConstants.NOT_SPECIFIED:
	    case TagConstants.NOTHINGEXPR:
	    case TagConstants.NOTSPECIFIEDEXPR:
		// FIXME - check the context???
		break;

            case TagConstants.UNINITIALIZED:
                if( ctxt.getTag() != TagConstants.LOCALVARDECL ) {
                    int loc;
                    if (ctxt instanceof GenericVarDecl)
                        loc = ((GenericVarDecl)ctxt).locId;
                    else
                        loc = p.getStartLoc();
                    ErrorSet.error(loc,
                                   "The uninitialized annotation can occur only on "
                                   +"local variable declarations");
                } else if( ((LocalVarDecl)ctxt).init == null ) {
                    ErrorSet.error(((GenericVarDecl)ctxt).locId,
                                   "The uninitialized annotation can occur only on "
                                   +"local variable declarations "
                                   +"that have an initializer");
                }
                break;
      
            case TagConstants.MONITORED:
                {
                    if( ctxt.getTag() != TagConstants.FIELDDECL ) {
                        int loc;
                        if (ctxt instanceof GenericVarDecl)
                            loc = ((GenericVarDecl)ctxt).locId;
                        else
                            loc = p.getStartLoc();
                        ErrorSet.error(loc,
                                       "The monitored annotation can occur only on "
                                       +"field declarations");
                    } else if (env.isStaticContext()) {
                        FieldDecl fd = (FieldDecl)ctxt;
                        ErrorSet.error(fd.locId,
                                       "The monitored annotation can occur only on "+
                                       "instance field declarations");
                    }
                    break;
                }

            case TagConstants.NON_NULL:
                // NOTE:  Part of the NON_NULL check is found in checkTypeDeclElem()
                // above, since there's not enough context information here to
                // determine whether a formal parameter is declared for a method
                // override.
                switch (ctxt.getTag()) {
                    case TagConstants.FORMALPARADECL:
                    case TagConstants.LOCALVARDECL:
                    case TagConstants.FIELDDECL: {
                        GenericVarDecl vd = (GenericVarDecl)ctxt;
                        if (! Types.isReferenceType(vd.type)) {
                            ErrorSet.error(vd.locId,
                                           "The non_null pragma can be applied only to "+
                                           "variables, fields, and parameters of "+
                                           "reference types");
                        }
                        break;
                    }
                    case TagConstants.METHODDECL: {
                        MethodDecl md = (MethodDecl) ctxt;
                        if (!Types.isReferenceType(md.returnType)) {
                            ErrorSet.error(md.getStartLoc(),
                                           "'non_null' can only be used with methods whose "+
                                           "result type is a reference type");
                        }
                        break;
                    }
                    default:
                        ErrorSet.error(p.getStartLoc(),
                                       "The non_null pragma can be applied only to "+
                                       "variables, fields, parameters, and methods");
                        break;
                }
                break;
      
// FIXME - should have aspec_protected case as well ???
            case TagConstants.SPEC_PUBLIC:
                {
		    int ctag = ctxt.getTag();
                    if( ctag == TagConstants.FIELDDECL ) {
                        FieldDecl fd = (FieldDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
			       "The spec_public annotation can occur only on "
			       +"non-public declarations");
                        }
                    } else if ( ctag == TagConstants.METHODDECL ) {
                        MethodDecl fd = (MethodDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
			       "The spec_public annotation can occur only on "
			       +"non-public declarations");
                        }
                    } else if ( ctag == TagConstants.CONSTRUCTORDECL ) {
                        RoutineDecl fd = (RoutineDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
			       "The spec_public annotation can occur only on "
			       +"non-public declarations");
                        }
                    } else if ( ctag == TagConstants.CLASSDECL  ||
			        ctag == TagConstants.INTERFACEDECL) {
                        TypeDecl fd = (TypeDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
			       "The spec_public annotation can occur only on "
			       +"non-public declarations");
                        }
		    }
                    break;
                }

            case TagConstants.SPEC_PROTECTED:
		{
		    int ctag = ctxt.getTag();
                    if( ctag == TagConstants.FIELDDECL ) {
                        FieldDecl fd = (FieldDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers) ||
			    Modifiers.isProtected(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
			       "The spec_protected annotation can occur only on "
			       +"non-public, non-protected declarations");
                        }
                    } else if ( ctag == TagConstants.METHODDECL ) {
                        MethodDecl fd = (MethodDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers) ||
			    Modifiers.isProtected(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
			       "The spec_protected annotation can occur only on "
			       +"non-public, non-protected declarations");
                        }
                    } else if ( ctag == TagConstants.CONSTRUCTORDECL ) {
                        RoutineDecl fd = (RoutineDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers) ||
			    Modifiers.isProtected(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
			       "The spec_protected annotation can occur only on "
			       +"non-public, non-protected declarations");
                        }
                    } else if ( ctag == TagConstants.CLASSDECL  ||
			        ctag == TagConstants.INTERFACEDECL) {
                        TypeDecl fd = (TypeDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers) ||
			    Modifiers.isProtected(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
			       "The spec_protected annotation can occur only on "
			       +"non-public, non-protected declarations");
                        }
		    }
                    break;
                }
	
            case TagConstants.WRITABLE_DEFERRED: 
                {
                    if (ctxt.getTag() != TagConstants.FIELDDECL ||
                        Modifiers.isStatic(((FieldDecl)ctxt).modifiers)) {
                        ErrorSet.error(p.getStartLoc(),
			   "The writable_deferred annotation can occur only on "
			   +"instance field declarations");
                    }
                    break;
                }

	    case TagConstants.INSTANCE:
	        {
		    int ctag = ctxt.getTag();
/*
		    if (!(ctxt instanceof GhostDeclPragma) &&
			!(ctxt instanceof ModelDeclPragma)) 
			ErrorSet.error(p.getStartLoc(),
			"An instance modifier may only be applied to ghost and model fields");
*/
		    break;
// FIXME - what about model methods???
		}

	    case TagConstants.PURE:
		{
		    // Actually, these are set in AnnotationHandler.
		    if (ctxt instanceof ConstructorDecl) {
			((ConstructorDecl)ctxt).modifiers |= Modifiers.ACC_PURE;
		    } else if (ctxt instanceof MethodDecl) {
			((MethodDecl)ctxt).modifiers |= Modifiers.ACC_PURE;
		    } else if (ctxt instanceof ClassDecl) {
			((ClassDecl)ctxt).modifiers |= Modifiers.ACC_PURE;
		    } else if (ctxt instanceof InterfaceDecl) {
			((InterfaceDecl)ctxt).modifiers |= Modifiers.ACC_PURE;
		    } else {
			ErrorSet.error(p.getStartLoc(),
				"Expected pure to modify a class, interface, constructor or method declaration");
		    }
		    break;
		}

            case TagConstants.HELPER:
                switch (ctxt.getTag()) {
                    case TagConstants.CONSTRUCTORDECL:
			((ConstructorDecl)ctxt).modifiers |= Modifiers.ACC_HELPER;
                        break;
                    case TagConstants.METHODDECL:
                        {
                            MethodDecl md = (MethodDecl) ctxt;
			    md.modifiers |= Modifiers.ACC_HELPER;
                            if (getOverrideStatus(md) != MSTATUS_NEW_ROUTINE) {
                                ErrorSet.error(p.getStartLoc(),
                                               "The helper pragma cannot be " +
                                               "applied to a method override");
                            } else if (isOverridable(md)) {
                                ErrorSet.error(p.getStartLoc(),
                                               "The helper pragma cannot be applied " +
                                               "to method that can be overridden");
                            } else if (md.body == null) {
                                ErrorSet.error(p.getStartLoc(),
                                               "The helper pragma cannot be applied " +
                                               "to method without a given body");
                            }
                            break;
                        }
                    default:
                        ErrorSet.error(p.getStartLoc(),
                                       "The helper pragma can only be applied to "+
                                       "methods and constructors");
                        break;
                }
                break;
	  
            case TagConstants.READABLE_IF:
                {
                    ExprModifierPragma emp = (ExprModifierPragma)p;

                    if( ctxt.getTag() != TagConstants.FIELDDECL
                        && ctxt.getTag() != TagConstants.LOCALVARDECL ) {
                        ErrorSet.error(p.getStartLoc(),
                                       "The readable_if annotation can occur only on "
                                       +"field declarations and "
                                       +"local variable declarations");
                    }

                    int oldAccessibilityLowerBound = accessibilityLowerBound;
                    ASTNode oldAccessibilityContext = accessibilityContext;
                    if (ctxt.getTag() == TagConstants.FIELDDECL) {
                        FieldDecl fd = (FieldDecl)ctxt;
                        accessibilityLowerBound = getAccessibility(fd.modifiers);
                        accessibilityContext = fd;
                    }
                    emp.expr = checkPredicate(env, emp.expr);
                    accessibilityLowerBound = oldAccessibilityLowerBound;
                    accessibilityContext = oldAccessibilityContext;
                    break;
                }

            case TagConstants.WRITABLE_IF:
                {
                    ExprModifierPragma emp = (ExprModifierPragma)p;

                    if( ctxt.getTag() != TagConstants.FIELDDECL
                        && ctxt.getTag() != TagConstants.LOCALVARDECL ) {
                        ErrorSet.error(p.getStartLoc(),
                                       "The writable_if annotation can occur only on "
                                       +"field declarations and "
                                       +"local variable declarations");
                    }

                    int oldAccessibilityLowerBound = accessibilityLowerBound;
                    ASTNode oldAccessibilityContext = accessibilityContext;
                    if (ctxt.getTag() == TagConstants.FIELDDECL) {
                        FieldDecl fd = (FieldDecl)ctxt;
                        accessibilityLowerBound = getAccessibility(fd.modifiers);
                        accessibilityContext = fd;
                    }
                    emp.expr = checkPredicate(env, emp.expr);
                    accessibilityLowerBound = oldAccessibilityLowerBound;
                    accessibilityContext = oldAccessibilityContext;
                    break;
                }

	    case TagConstants.NO_WACK_FORALL:
	    case TagConstants.OLD:
	        {
		    VarDeclModifierPragma vd = (VarDeclModifierPragma)p;
		    LocalVarDecl x = vd.decl;
		    checkTypeModifiers(env, x.type);
		    javafe.tc.PrepTypeDeclaration.inst.
			checkModifiers(x.modifiers, Modifiers.NONE,
			    x.locId, "local specification variable");

		    Env newEnv = new EnvForGhostLocals(env,x);
		    boolean savedContext = isTwoStateContext;
		    isTwoStateContext = true;
		    if (x.init != null) {
			//if (x.init instanceof ArrayInit) {
			    x.init = checkInit(newEnv, x.init, x.type);
			//} else {
			    //checkExpr(newEnv, (Expr)x.init, x.type);
			//}
		    }
		    isTwoStateContext = savedContext;
		    env = newEnv;
		    break;
		}

            case TagConstants.ALSO_REQUIRES:
            case TagConstants.REQUIRES:
            case TagConstants.PRECONDITION:
                {
                    ExprModifierPragma emp = (ExprModifierPragma)p;

                    if( !(ctxt instanceof RoutineDecl ) ) {
                        ErrorSet.error(p.getStartLoc(), TagConstants.toString(tag) +
                                       " annotations can occur only on method" +
                                       ((tag == TagConstants.REQUIRES || 
                                         tag == TagConstants.PRECONDITION) ? " and constructor" : "") +
                                       " declarations");
                    } else {
                        RoutineDecl rd = (RoutineDecl)ctxt;

                        int ms = getOverrideStatus(rd);

			Env newenv = env;
                        if (rd instanceof ConstructorDecl) {
                            newenv = env.asStaticContext();
                        }
                        int oldAccessibilityLowerBound = accessibilityLowerBound;
                        ASTNode oldAccessibilityContext = accessibilityContext;
                        accessibilityLowerBound = getAccessibility(rd.modifiers);
                        accessibilityContext = rd;
			if (emp.expr.getTag() != TagConstants.NOTSPECIFIEDEXPR)
			    emp.expr = checkPredicate(newenv, emp.expr);
                        accessibilityLowerBound = oldAccessibilityLowerBound;
                        accessibilityContext = oldAccessibilityContext;
                    }
                    break;
                }

	    case TagConstants.MEASURED_BY:
	    case TagConstants.DURATION:
	    case TagConstants.WORKING_SPACE:
	        {
                    CondExprModifierPragma emp = (CondExprModifierPragma)p;

                    if( !(ctxt instanceof RoutineDecl ) ) {
                        ErrorSet.error(p.getStartLoc(),
                                       TagConstants.toString(tag)
                                       +" annotations can occur only on "
                                       +"method and constructor declarations");
                    } else {
                        RoutineDecl rd = (RoutineDecl)ctxt;
                        boolean oldIsRESContext = isRESContext;
                        boolean oldIsTwoStateContext = isTwoStateContext;
                        boolean oldIsPrivFieldAccessAllowed = isPrivateFieldAccessAllowed;
                        isRESContext = true;
                        isTwoStateContext = true;
                        // If "rd" is an overridable method, then every private field
                        // mentioned in "emp.expr" must be spec_public.
                        if (rd instanceof MethodDecl && isOverridable((MethodDecl)rd)) {
                            isPrivateFieldAccessAllowed = false;
                        }
			if (tag == TagConstants.MEASURED_BY) {
				// FIXME - what type to use?
			    emp.expr = checkExpr(env, emp.expr);
			} else if (emp.expr.getTag() != TagConstants.NOTSPECIFIEDEXPR)
			    emp.expr = checkExpr(env, emp.expr, Types.longType);
                        if (emp.cond != null)
			 emp.cond = checkExpr(env, emp.cond, Types.booleanType);
                        isRESContext = oldIsRESContext;
                        isTwoStateContext = oldIsTwoStateContext;
                        isPrivateFieldAccessAllowed = oldIsPrivFieldAccessAllowed;
                    }
                    break;
                }

	    case TagConstants.DIVERGES:
            case TagConstants.ENSURES:
            case TagConstants.ALSO_ENSURES:
            case TagConstants.POSTCONDITION:
	    case TagConstants.WHEN:
                {
                    ExprModifierPragma emp = (ExprModifierPragma)p;

                    if( !(ctxt instanceof RoutineDecl ) ) {
                        ErrorSet.error(p.getStartLoc(),
                                       TagConstants.toString(tag)
                                       +" annotations can occur only on "
                                       +"method and constructor declarations");
                    } else {
                        RoutineDecl rd = (RoutineDecl)ctxt;
                        boolean oldIsRESContext = isRESContext;
                        boolean oldIsTwoStateContext = isTwoStateContext;
                        boolean oldIsPrivFieldAccessAllowed = isPrivateFieldAccessAllowed;
                        isRESContext = true;
                        isTwoStateContext = true;
                        // If "rd" is an overridable method, then every private field
                        // mentioned in "emp.expr" must be spec_public.
                        if (rd instanceof MethodDecl && isOverridable((MethodDecl)rd)) {
                            isPrivateFieldAccessAllowed = false;
                        }
			if (emp.expr.getTag() != TagConstants.NOTSPECIFIEDEXPR)
			    emp.expr = checkPredicate(env, emp.expr);
                        isRESContext = oldIsRESContext;
                        isTwoStateContext = oldIsTwoStateContext;
                        isPrivateFieldAccessAllowed = oldIsPrivFieldAccessAllowed;
                    }
                    break;
                }


            case TagConstants.EXSURES:
            case TagConstants.ALSO_EXSURES:
            case TagConstants.SIGNALS:
                {
                    VarExprModifierPragma vemp = (VarExprModifierPragma)p;

                    if( !(ctxt instanceof RoutineDecl ) ) {
                        ErrorSet.error(p.getStartLoc(),
                                       TagConstants.toString(tag)
                                       +" annotations can occur only on "
                                       +"method and constructor declarations");
                    } else {
                        RoutineDecl rd = (RoutineDecl)ctxt;

                        // Resolve type and check that it is a subtype of Throwable
                        // and comparable to some type mentioned in the throws set.
                        env.resolveType(vemp.arg.type);
                        if (!Types.isSubclassOf(vemp.arg.type,
                                                Types.javaLangThrowable())) {
                            ErrorSet.error(vemp.arg.type.getStartLoc(),
                                           "The type of the " +
                                           TagConstants.toString(tag) +
                                           " argument must be a subtype of " +
                                           "java.lang.Throwable");
                        } else {
                            // "vemp.arg.type" is a subclass of "Throwable", so it
                            // must be a "TypeName" or a "TypeSig"
                            TypeSig ssig;
                            if (vemp.arg.type instanceof TypeSig) {
                                ssig = (TypeSig)vemp.arg.type;
                            } else {
                                ssig = TypeSig.getSig((TypeName)vemp.arg.type);
                            }
                            boolean okay = false;
                            for (int i = 0; i < rd.raises.size(); i++) {
                                TypeName tn = rd.raises.elementAt(i);
                                TypeSig tsig = TypeSig.getSig(tn);
                                if (Types.isSubclassOf(ssig, tsig) ||
                                    Types.isSubclassOf(tsig, ssig)) {
                                    okay = true;
                                    break;
                                }
                            }
                            if (!okay) {
				if (!( (vemp.expr instanceof LiteralExpr) &&
					((LiteralExpr)vemp.expr).value.equals(Boolean.FALSE))) {
/* FIXME - what about Error exceptions, must they be mentioned?  */
/* FIXME
                                ErrorSet.error(vemp.arg.type.getStartLoc(),
				   "The type of the " +
				   TagConstants.toString(tag) +
				   " argument must be comparable to some type"+
				   " mentioned in the routine's throws set");
*/
				}
                            }
                        }

                        Env subenv = new EnvForLocals(env, vemp.arg);
// FIXME - below we say that this is a twostate context, in which case we should not set this to static???
                        if (rd instanceof ConstructorDecl) {
                            subenv = subenv.asStaticContext();
                        }

                        // Check the expression to be an appropriate predicate
                        boolean oldIsTwoStateContext = isTwoStateContext;
                        boolean oldIsPrivFieldAccessAllowed = isPrivateFieldAccessAllowed;
                        isTwoStateContext = true;
                        // If "rd" is an overridable method, then every private field
                        // mentioned in "emp.expr" must be spec_public.
                        if (rd instanceof MethodDecl && isOverridable((MethodDecl)rd)) {
                            isPrivateFieldAccessAllowed = false;
                        }
			if (vemp.expr.getTag() != TagConstants.NOTSPECIFIEDEXPR)
			    vemp.expr = checkPredicate(subenv, vemp.expr);
                        isTwoStateContext = oldIsTwoStateContext;
                        isPrivateFieldAccessAllowed = oldIsPrivFieldAccessAllowed;
                    }
                    break;
                }

            case TagConstants.MONITORED_BY: {
                ExprModifierPragma emp = (ExprModifierPragma)p;

                if (ctxt.getTag() != TagConstants.FIELDDECL) {
                    ErrorSet.error(p.getStartLoc(),
                                   "The monitored_by annotation can occur only on "+
                                   "field declarations");
                } else {
                    FieldDecl fd = (FieldDecl)ctxt;

                    int oldAccessibilityLowerBound = accessibilityLowerBound;
                    ASTNode oldAccessibilityContext = accessibilityContext;
                    accessibilityLowerBound = getAccessibility(fd.modifiers);
                    accessibilityContext = fd;
                    emp.expr = checkExpr(env, emp.expr, Types.javaLangObject());
                    accessibilityLowerBound = oldAccessibilityLowerBound;
                    accessibilityContext = oldAccessibilityContext;
                }
                break;
            }

	    case TagConstants.MODIFIES:
            case TagConstants.ASSIGNABLE:
            case TagConstants.MODIFIABLE:
            case TagConstants.STILL_DEFERRED: {
                CondExprModifierPragma emp = (CondExprModifierPragma)p;

                if (!(ctxt instanceof RoutineDecl ) ) {
                    ErrorSet.error(p.getStartLoc(),
                                   "A modifies annotation " +
                                   "can occur only on " +
                                   "method and constructor declarations");
                } else {
                    RoutineDecl rd = (RoutineDecl)ctxt;
	    
                    Assert.notFalse(!isSpecDesignatorContext);
                    isSpecDesignatorContext = true;
		    Env newenv = env;
/*
// But we do need to allow the fields of this in the modifies clause, which
// using the static context does not permit.
                        if (rd instanceof ConstructorDecl) {
                            // disallow "this" from constructor "modifies" clauses
                            newenv = env.asStaticContext();
                        }
*/
                    emp.expr = checkDesignator(newenv, emp.expr);
                    switch (emp.expr.getTag()) {
                        case TagConstants.FIELDACCESS: {
                            FieldAccess fa = (FieldAccess)emp.expr;
                            if (fa.decl != null &&
                                Modifiers.isFinal(fa.decl.modifiers) &&
                                // The array "length" field has already been checked
                                // insuper.checkDesignator().
                                fa.decl != Types.lengthFieldDecl) {
                                ErrorSet.error(fa.locId, "a final field is not allowed as " +
                                               "the designator in a modifies clause");
                            }
                            break;
                        }
	  
			case TagConstants.ARRAYREFEXPR:
			case TagConstants.WILDREFEXPR:
			case TagConstants.EVERYTHINGEXPR:
			case TagConstants.NOTHINGEXPR:
			case TagConstants.NOTSPECIFIEDEXPR:
			    break;

			default:
			    if (escjava.parser.EscPragmaParser.
				 informalPredicateDecoration.get(emp.expr)==null) {
					// The expression is not a designator
					// but we allow an informal predicate
                                ErrorSet.error(emp.expr.getStartLoc(),
                                               "Not a specification designator expression");
			    } else {
			       emp.expr = null;
			    }
                    }
		    if (rd instanceof MethodDecl && isPure(rd) &&
			emp.expr != null && emp.expr.getTag() != TagConstants.NOTHINGEXPR) {
			ErrorSet.error(p.getStartLoc(),
				"A pure method may not have a modifies clause");
				// FIXME - point to the pure designation
		    }
                    isSpecDesignatorContext = false;
                    if (emp.cond != null) emp.cond = checkExpr(newenv, emp.cond);
                }
                break;
            }

	    case TagConstants.ALSO:
	    case TagConstants.ALSO_REFINE:
	    case TagConstants.MODEL_PROGRAM:
	    case TagConstants.BEHAVIOR:
	    case TagConstants.CLOSEPRAGMA:
	    case TagConstants.EXAMPLE:
	    case TagConstants.EXCEPTIONAL_BEHAVIOR:
	    case TagConstants.EXCEPTIONAL_EXAMPLE:
	    case TagConstants.FOR_EXAMPLE:
	    case TagConstants.IMPLIES_THAT:
	    case TagConstants.NORMAL_BEHAVIOR:
	    case TagConstants.NORMAL_EXAMPLE:
	    case TagConstants.OPENPRAGMA:
		// Desugaring happens before type-checking,
		// This shouldn't happen.
		break;

	    case TagConstants.GHOST:
	    case TagConstants.MODEL:
		break;

	    case TagConstants.NESTEDMODIFIERPRAGMA:
	      {
		java.util.ArrayList list = ((NestedModifierPragma)p).list;
		java.util.Iterator i = list.iterator();
		while (i.hasNext()) {
		    ModifierPragmaVec mpv = (ModifierPragmaVec)i.next();
		    checkModifierPragmaVec(mpv,ctxt,env);
		}
		break;
	      }

	    case TagConstants.PARSEDSPECS:
	      {
		escjava.ParsedRoutineSpecs pp = ((ParsedSpecs)p).specs;
		java.util.Iterator i = pp.specs.iterator();
		while (i.hasNext()) {
		    checkModifierPragmaVec((ModifierPragmaVec)i.next(),ctxt,env);    
		}
		i = pp.impliesThat.iterator();
		while (i.hasNext()) {
		    checkModifierPragmaVec((ModifierPragmaVec)i.next(),ctxt,env);    
		}
		i = pp.examples.iterator();
		while (i.hasNext()) {
		    checkModifierPragmaVec((ModifierPragmaVec)i.next(),ctxt,env);    
		}
/* This duplicates stuff
		// The last element is the ParsedSpecs containing all the
		// clauses etc.
		ModifierPragmaVec mpv = pp.modifiers;
		ModifierPragma last = mpv.elementAt(mpv.size()-1);
		mpv.removeElementAt(mpv.size()-1);
		checkModifierPragmaVec(mpv,ctxt,env);
		mpv.addElement(last);
*/
		break;
	      }

	    case TagConstants.IN:
	    case TagConstants.MAPS:
		//System.out.println("FOUND " + TagConstants.toString(tag) + " for " + ((FieldDecl)ctxt).id );
		break;

            default:
                ErrorSet.error(p.getStartLoc(),
				"Ignored unexpected " +  
				TagConstants.toString(tag) +
				" tag");
		break;
        }
        inAnnotation = savedInAnnotation;
	return env;
    }

    /**
     * @return whether or not <code>md</code> can be overridden in some possible
     * subclass.
     */

    public static boolean isOverridable(/*@ non_null */ MethodDecl md) {
        return !(Modifiers.isPrivate(md.modifiers) ||
                 Modifiers.isFinal(md.modifiers) ||
                 Modifiers.isFinal(md.parent.modifiers) ||
                 Modifiers.isStatic(md.modifiers));
    }

    /**
     * @return a value appropriate for assignment to
     * <code>accessibilityLowerBound</code>, given member modifiers.
     */

    protected int getAccessibility(int modifiers) {
        if (Modifiers.isPrivate(modifiers)) {
            return ACC_LOW_BOUND_Private;
        } else if (Modifiers.isPackage(modifiers)) {
            return ACC_LOW_BOUND_Package;
        } else if (Modifiers.isProtected(modifiers)) {
            return ACC_LOW_BOUND_Protected;
        } else {
            Assert.notFalse(Modifiers.isPublic(modifiers));
            return ACC_LOW_BOUND_Public;
        }
    }

    protected Env checkStmtPragma(Env e, StmtPragma s) {
	boolean savedInAnnotation = inAnnotation;
        inAnnotation = true;	// Must be reset before we exit!
        int tag = s.getTag();
        switch(tag) {
            case TagConstants.UNREACHABLE:
                break;

            case TagConstants.SETSTMTPRAGMA: {
                SetStmtPragma set = (SetStmtPragma)s;
                set.target = checkExpr(e, set.target);
                set.value = checkExpr(e, set.value);
                checkBinaryExpr(TagConstants.ASSIGN, set.target,
                                set.value, set.locOp);
		Expr t = set.target;
		int nonGhostLoc = isGhost(t);
		if (nonGhostLoc != 0) {
		    ErrorSet.error(s.getStartLoc(),"May use set only with assignment targets that are declared ghost",nonGhostLoc);
		}
/*
		if (t instanceof FieldAccess &&
		    ((FieldAccess)t).decl == Types.lengthFieldDecl) {
		    ErrorSet.error(s.getStartLoc(),"The length field of an array may not be set");
		}
*/
                break;
            }

            case TagConstants.ASSUME:
            case TagConstants.ASSERT:
		{
		    ExprStmtPragma es = (ExprStmtPragma)s;
		    es.expr = checkPredicate(e, es.expr);
		    break;
		}
      
            case TagConstants.LOOP_INVARIANT:
            case TagConstants.MAINTAINING:
                {
                    ExprStmtPragma lis = (ExprStmtPragma)s;
                    loopInvariants.addElement(lis);
                    break;
                }

            case TagConstants.DECREASES:
            case TagConstants.DECREASING:
                {
                    ExprStmtPragma lis = (ExprStmtPragma)s;
                    loopDecreases.addElement(lis);
                    break;
                }

            case TagConstants.LOOP_PREDICATE:
                {
                    ExprStmtPragma lis = (ExprStmtPragma)s;
                    loopPredicates.addElement(lis);
                    break;
                }

            case TagConstants.SKOLEMCONSTANTPRAGMA:
                {
                    SkolemConstantPragma p = (SkolemConstantPragma)s;
                    skolemConstants.append(p.decls);
                    break;
                }

            default:
                Assert.fail("Unexpected tag " + tag +" "+s +
				" " + Location.toString(s.getStartLoc()));
        }
        inAnnotation = savedInAnnotation;
	return e;
    }


    // Utility routines

    /**
     * Copy the Type associated with an expression by the typechecking pass to
     * another Expr.  This is used by Substitute to ensure it returns an Expr of the
     * same Type.
     */
    public static void copyType(VarInit from, VarInit to) {
	Type t = getTypeOrNull(from);
	if (t != null)
	    setType(to, t);
    }

    /**
     * @return a set of *all* the methods a given method overrides. This includes
     * transitivity.
     */
    //@ requires md != null
    //@ ensures \result != null
    //@ ensures \result.elementType == \type(MethodDecl);
    public static Set getAllOverrides(MethodDecl md) {
	Set direct = javafe.tc.PrepTypeDeclaration.inst.getOverrides(md.parent, md);
	Set result = new Set();

	Enumeration e = direct.elements();
	while (e.hasMoreElements()) {
	    MethodDecl directMD = (MethodDecl)(e.nextElement());
	    result.add(directMD);
	    result.addEnumeration(getAllOverrides(directMD).elements());
	}

	return result;
    }

    public static javafe.util.Set getDirectOverrides(MethodDecl md) {
	return javafe.tc.PrepTypeDeclaration.inst.getOverrides(md.parent, md);
    }

    /**
     * @return If <code>md</code> is a method that overrides a method in a
     * superclass, the overridden method is returned.  Otherwise, if <code>md</code>
     * overrides a method in an interface, such a method is returned.  Otherwise,
     * <code>null</code> is returned.
     */

    public static MethodDecl getSuperClassOverride(MethodDecl md) {
        MethodDecl classOverride = null;
        MethodDecl interfaceOverride = null;
        Set direct = javafe.tc.PrepTypeDeclaration.inst.getOverrides(md.parent, md);
        Enumeration e = direct.elements();
        while (e.hasMoreElements()) {
            MethodDecl directMD = (MethodDecl)(e.nextElement());
            if (directMD.parent instanceof ClassDecl) {
                if (classOverride == null) {
                    classOverride = directMD;
                } else {
                    Assert.fail("we think this can no longer happen!");
                    // This suggests that the method is inherited from TWO classes!
                    // This can actually happen, if the method is one that is
                    // declared in Object, because every interface has the methods of
                    // Object.  In this case, pick the method override that does not
                    // reside in Object.
                    Type javaLangObject = Types.javaLangObject();
                    Type t0 = TypeSig.getSig(classOverride.parent);
                    Type t1 = TypeSig.getSig(directMD.parent);
                    Assert.notFalse(Types.isSameType(t0, javaLangObject) ||
                                    Types.isSameType(t1, javaLangObject));
                    Assert.notFalse(!Types.isSameType(t0, javaLangObject) ||
                                    !Types.isSameType(t1, javaLangObject));
                    if (!Types.isSameType(t1, javaLangObject)) {
                        classOverride = directMD;
                    }
                }
            } else {
                interfaceOverride = directMD;
            }
        }
        if (classOverride != null) {
            return classOverride;
        } else {
            return interfaceOverride;
        }
    }

    /**
     * @return whether or not <code>rd</code> is a method override declaration, that
     * is, whether or not <code>rd</code> overrides a method declared in a superclass
     * or superinterface.
     */

    public static boolean isMethodOverride(RoutineDecl rd) {
        return getOverrideStatus(rd) != MSTATUS_NEW_ROUTINE;
    }	

    static public final int MSTATUS_NEW_ROUTINE = 0;
    static public final int MSTATUS_CLASS_NEW_METHOD = 1;
    static public final int MSTATUS_OVERRIDE = 2;

    /**
     * @return <code>MSTATUS_NEW_ROUTINE</code> if <code>rd</code> is a routine that
     * doesn't override any other method.  This includes the case where
     * <code>rd</code> is a constructor or a static method.
     *
     * <p> Returns <code>MSTATUS_CLASS_NEW_METHOD</code> if <code>rd</code> is a
     * method declared in a class, doesn't override any method in any superclass, but
     * overrides a method in an interface.
     *
     * <p> Otherwise, returns <code>MSTATUS_OVERRIDE</code>.
     */

    /*@ ensures \result == MSTATUS_NEW_ROUTINE ||
      @         \result == MSTATUS_CLASS_NEW_METHOD ||
      @         \result == MSTATUS_OVERRIDE; 
     */
    public static int getOverrideStatus(/*@ non_null */ RoutineDecl rd) {
        if (!(rd instanceof MethodDecl) || Modifiers.isStatic(rd.modifiers)) {
            return MSTATUS_NEW_ROUTINE;
        }
        MethodDecl md = (MethodDecl)rd;

        Set direct = javafe.tc.PrepTypeDeclaration.inst.getOverrides(md.parent, md);
        if (direct.size() == 0) {
            return MSTATUS_NEW_ROUTINE;
        }
        if (!(md.parent instanceof ClassDecl)) {
            return MSTATUS_OVERRIDE;
        }

        Enumeration e = direct.elements();
        while (e.hasMoreElements()) {
            MethodDecl directMD = (MethodDecl)(e.nextElement());
            if (directMD.parent instanceof ClassDecl) {
                return MSTATUS_OVERRIDE;
            }
        }
        return MSTATUS_CLASS_NEW_METHOD;
    }

    /**
     * @return null if method md is allowed to declare its jth (counting from 0)
     * formal parameter as non_null.  That is the case if the method does not
     * override anything, or if in everything that it does override that parameter is
     * declared non_null.  Otherwise returns the MethodDecl corresponding to the
     * overridden method with which the argument rd is in conflict.
     */
    static public MethodDecl getSuperNonNullStatus(RoutineDecl rd, int j) {
        if (!(rd instanceof MethodDecl) || Modifiers.isStatic(rd.modifiers)) {
            return null;
        }
        MethodDecl md = (MethodDecl)rd;

        Set direct = javafe.tc.PrepTypeDeclaration.inst.getOverrides(md.parent, md);
        if (direct.size() == 0) {
            return null;
        }
	return getSuperNonNullStatus(rd,j,direct);
    }

    static public MethodDecl getSuperNonNullStatus(RoutineDecl rd, int j, Set directOverrides) {
        Enumeration e = directOverrides.elements();
        while (e.hasMoreElements()) {
            MethodDecl directMD = (MethodDecl)(e.nextElement());
	    FormalParaDecl f = directMD.args.elementAt(j);
	    if (GetSpec.findModifierPragma(f,TagConstants.NON_NULL) == null)
		return directMD;
        }
        return null;
    }

    /**
     * @return true if directly or indirectly pure.
     */
    static public boolean isPure(RoutineDecl rd) {
	if ((rd.modifiers & Modifiers.ACC_PURE_CLOSURE)!=0) return true;
	if ((rd.modifiers & Modifiers.ACC_IMPURE_CLOSURE)!=0) return false;
	boolean b = Modifiers.isPure(rd.modifiers) ||   // pure on the routine
		 Modifiers.isPure(rd.parent.modifiers); // pure on the class
	if (b) { rd.modifiers |= Modifiers.ACC_PURE_CLOSURE; return b; }
	// find and test interfaces and extendsions
	if (rd instanceof MethodDecl) {
	    MethodDecl md = (MethodDecl)rd;
	    Set direct = javafe.tc.PrepTypeDeclaration.inst.getOverrides(md.parent, md);
	    Enumeration e = direct.elements();
	    while (e.hasMoreElements()) {
		MethodDecl directMD = (MethodDecl)(e.nextElement());
		if (isPure(directMD)) {
		    md.modifiers |= Modifiers.ACC_PURE_CLOSURE;
		    return true;
		}
	    }
        }
	rd.modifiers |= Modifiers.ACC_IMPURE_CLOSURE;
	return false;
    }


    /** Returns non-zero if the expression is a ghost expression - that is, it
	would not exist if all ghost declarations were removed.  Otherwise
	returns a Location value of a relevant non-ghost declaration.
     */
    public int isGhost(Expr t) {
	if (t instanceof ArrayRefExpr) {
	    t = ((ArrayRefExpr)t).array;
	}
	if (t instanceof FieldAccess) {
	    FieldAccess fa = (FieldAccess)t;
	    if (fa.decl == null || GhostEnv.isGhostField(fa.decl))
		return 0;
	    int gl = isGhost(fa.od);
	    if (gl == 0) return 0;
	    if (gl == -1) return fa.decl.getStartLoc();
	    return gl;
	} else if (t instanceof VariableAccess) {
	    VariableAccess va = (VariableAccess)t;
	    GenericVarDecl gd = va.decl;
	    if ( escjava.translate.GetSpec.findModifierPragma(
			gd.pmodifiers,TagConstants.GHOST) == null)
		return gd.getStartLoc();
	} else if (t instanceof ParenExpr) {
	    return isGhost( ((ParenExpr)t).expr );
	} else if (t instanceof CastExpr) {
	    return isGhost( ((CastExpr)t).expr );
	}
	return 0;
	// FIXME - need some test that the expression in advance of
	// a . in a field reference or the [] in an array reference
	    // only designates ghost fields/variables
		// e.g. what about method calls, operator expressions?

    }

    public int isGhost(ObjectDesignator od) {
	if (od instanceof ExprObjectDesignator) {
	    Expr e = ((ExprObjectDesignator)od).expr;
	    if (e == null || e instanceof ThisExpr) return -1;
	    return isGhost(e);
	}
	return -1; // OK for TypeObjectDesignator and SuperObjectDesignator
    }
} // end of class FlowInsensitiveChecks

/*
 * Local Variables:
 * Mode: Java
 * fill-column: 85
 * End:
 */
