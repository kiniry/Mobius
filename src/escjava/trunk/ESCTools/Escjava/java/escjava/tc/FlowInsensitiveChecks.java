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
     * Are we in the middle of processing an annotation?
     *
     * <p> (Used by GhostEnv) </p>
     */
    public static boolean inAnnotation = false;

    /**
     * Indicates whether <code>LS</code> is allowed in this context.
     * The default is <code>true</code>.  For contexts where
     * <code>LS</code> is not allowed, <code>isLocksetContext</code>
     * should be set <code>false</code> only temporarily.
     */
    protected boolean isLocksetContext = true;

    /**
     * <code>\result</code> is allowed in this context when
     * <code>isRESContext</code> is <code>true</code> and
     * <code>returnType != null</code>.  The default value of
     * <code>isRESContext</code> is <code>false</code>.  For contexts
     * where <code>isRESContext</code> should be <code>true</code>,
     * <code>isRESContext</code> should be set to <code>true</code>
     * only temporarily.
     */
    protected boolean isRESContext = false;

    /**
     * Indicates whether <code>\old</code> and <code>\fresh</code> are
     * allowed in this context.  The default is <code>false</code>.
     * For contexts where these functions are allowed,
     * <code>isTwoStateContext</code> should be set <code>true</code>
     * only temporarily.
     */
    protected boolean isTwoStateContext = false;

    /**
     * Indicates whether checking is currently being done inside a
     * <code>PRE</code>.  This is used by the code that disallows
     * nested <code>PRE</code> expressions.  Note: alternatively, one
     * could use <code>isTwoStateContext</code> to implement this
     * functionality, but by having a separate bit, a more precise
     * error message can be produced.
     */
    protected boolean isInsidePRE = false;

    /**
     * Indicates whether a quantification or labeled predicate is
     * allowed in this context.  This boolean is used only between one
     * call of <code>checkExpr</code> to a following recursive call.
     */
    protected boolean isPredicateContext = false;

    /**
     * Indicates whether private field accesses are allowed in the
     * current context.  Private field accesses are allowed
     * everywhere, except in postconditions of overridable methods.
     */
    protected boolean isPrivateFieldAccessAllowed = true;

    protected int accessibilityLowerBound = ACC_LOW_BOUND_Private;
    // Note, "ACC_LOW_BOUND_Private" would be the same as "no lower bound"
    protected static final int ACC_LOW_BOUND_Private = 0;
    protected static final int ACC_LOW_BOUND_Package = 1;
    protected static final int ACC_LOW_BOUND_Protected = 2;
    protected static final int ACC_LOW_BOUND_Public = 3;

    /**
     * If <code>accessibilityLowerBound !=
     * ACC_LOW_BOUND_Private</code>, then
     * <code>accessibilityContext</code> is the field or routine whose
     * modifier pragma is being type checked.
     */
    /*@ invariant accessibilityContext == null ||
     accessibilityContext instanceof FieldDecl ||
     accessibilityContext instanceof RoutineDecl; */
    //@ readable_if accessibilityLowerBound != ACC_LOW_BOUND_Private;
    protected ASTNode accessibilityContext;

    /**
     * Acts as a parameter to <code>checkExpr</code>.  Its value is
     * meaningful only on entry to <code>checkExpr</code>.  It
     * indicates whether the expression to be checked is in a
     * specification designator context.  In particular, this
     * parameter is used to disallow array index wild cards in
     * non-spec designator contexts.
     */
    protected boolean isSpecDesignatorContext = false;
  
    /**
     * Contains the loop invariant statement pragmas seen so far and
     * not yet processed.
     */
    protected ExprStmtPragmaVec loopInvariants = ExprStmtPragmaVec.make();

    /**
     * Contains the loop decreases statement pragmas seen so far and
     * not yet processed.
     */
    protected ExprStmtPragmaVec loopDecreases = ExprStmtPragmaVec.make();

    protected ExprStmtPragmaVec loopPredicates = ExprStmtPragmaVec.make();

    protected LocalVarDeclVec skolemConstants = LocalVarDeclVec.make();

    /**
     * Indicates whether we are are checking an invariant pragma.
     */
    protected boolean invariantContext = false;

    /**
     * Counts the number of accesses of free variables and fields used
     * for checking the appropriateness of invariants.
     */
    //@ readable_if invariantContext;
    protected int countFreeVarsAccesses =0 ;

    /**
     * Override so that we use GhostEnv instead of EnvForTypeSig.
     */
    protected EnvForTypeSig makeEnvForTypeSig(TypeSig s,
					      boolean staticContext) {
	return new GhostEnv(s.getEnclosingEnv(), s, staticContext);
    }
  

    // Extensions to type declaration member checkers

    protected void checkTypeDeclElem(TypeDeclElem e) {
        super.checkTypeDeclElem(e);
    
        if (e.getTag() == TagConstants.METHODDECL) {
            MethodDecl md = (MethodDecl)e;
            if (getOverrideStatus(md) != MSTATUS_NEW_ROUTINE) {
                for (int j = 0; j < md.args.size(); j++) {
                    FormalParaDecl formal = md.args.elementAt(j);
                    // Note:  One calls GetSpec.NonNullPragma() to find out
                    // whether a variable is non_null.  The NonNullPragma() method
                    // properly handles inheritance of non_null for parameters.
                    // However, in this case the information needed is whether
                    // or not the formal parameter has been declared with a
                    // "non_null" pragma.
                    ModifierPragma mp = GetSpec.findModifierPragma(formal,
                                                                   TagConstants.NON_NULL);
                    if (mp != null) {
                        ErrorSet.error(mp.getStartLoc(),
                                       TagConstants.toString(TagConstants.NON_NULL) +
                                       " cannot be applied to parameters of a" +
                                       " method override");
                    }
                }
            }
        } else if (e.getTag() == TagConstants.INITBLOCK) {
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


    // Extensions to Expr and Stmt checkers

    protected Env checkStmt(Env env, Stmt s) {
        int tag = s.getTag();

        // Check for any loop invariants, loop bounds, loop predicates, or
        // skolem constants in the wrong place
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
                case TagConstants.JML_MAINTAINING:
                case TagConstants.DECREASES:
                case TagConstants.JML_DECREASING:
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
                // Check for any loop_invariant statement pragmas at the end of the body
                checkLoopInvariants(env, false);
                checkLoopDecreases(env, false);
                checkLoopPredicates(env, false);
                checkSkolemConstants(env, false);
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
                            || s.getTag() == TagConstants.JML_MAINTAINING);
            if (allowed) {
                Assert.notFalse(!isTwoStateContext);
                Assert.notFalse(!inAnnotation);
                inAnnotation = true;
                isTwoStateContext = true;
                s.expr = checkPredicate(env, s.expr);
                inAnnotation = false;
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
                            || s.getTag() == TagConstants.JML_DECREASING);
            if (allowed) {
                Assert.notFalse(!isTwoStateContext);
                Assert.notFalse(!inAnnotation);
                inAnnotation = true;
                s.expr = checkExpr(env, s.expr, Types.intType);
                inAnnotation = false;
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
                inAnnotation = true;
                isTwoStateContext = true;
                s.expr = checkPredicate(env, s.expr);
                inAnnotation = false;
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
                inAnnotation = true;
                isTwoStateContext = true;
                env.resolveType(s.type);
                env = new EnvForLocals(env, s);
                inAnnotation = false;
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
     * Not to be used as a recursive call from <code>checkExpr</code>,
     * since <code>isPredicateContext</code> is set to <code>true</code>.
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
        // Anticipate that the next context is probably not one suitable
        // for quantifications and labels.  "isPredicateContext" must
        // revert to its old value before return from
        boolean isCurrentlyPredicateContext = isPredicateContext;
        isPredicateContext = false;

        if (getTypeOrNull(e) != null )
            // already done
            return e;

        // No recursive call to "checkExpr" is a specification designator
        // context, so set "isSpecDesignatorContext" to "false", keeping
        // the initial value in local variable "isCurrentlySpecDesignatorContext".
        boolean isCurrentlySpecDesignatorContext = isSpecDesignatorContext;
        isSpecDesignatorContext = false;
    
        int tag = e.getTag();
        switch(tag) {

            // Handle accesses to ghost fields as well...
            case TagConstants.FIELDACCESS:
                {
                    if (!inAnnotation)
                        return super.checkExpr(env, e);
	
                    // a field access is considerded a free variable access in 
                    // an invariant
                    if (invariantContext) countFreeVarsAccesses++;

                    // set default result type to integer, in case there is an error
                    setType( e, Types.intType );
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
                        !Modifiers.isStatic(fa.decl.modifiers)) {
                        // Is fa.decl an instance field of the same class as
                        // fa is part of?
                        boolean thisField = false;
                        if (fa.decl.parent != null)
                            thisField = (env.getEnclosingClass()
                                         .isSubtypeOf(TypeSig.getSig(fa.decl.parent)));
	    
                        if (thisField ||
                            ((TypeObjectDesignator)fa.od).type instanceof TypeName)
                            ErrorSet.error(fa.locId,
                                           "An instance field may be accessed only via "
                                           + "an object and/or from a non-static"
                                           + " context or an inner class enclosed"
                                           + " by a type possessing that field.");
                        else
                            ErrorSet.error(fa.locId,
                                           "The instance fields of type "
                                           + ((TypeObjectDesignator)fa.od).type
                                           + " may not be accessed from type "
                                           + sig);
                    }

                    if (!isPrivateFieldAccessAllowed &&
                        Modifiers.isPrivate(fa.decl.modifiers) &&
                        GetSpec.findModifierPragma(fa.decl,
                                                   TagConstants.SPEC_PUBLIC) == null) {
                        ErrorSet.error(fa.locId, "A private field can be used in "+
                                       "postconditions of overridable methods "+
                                       "only if it is declared spec_public");
                    }

                    // The following code checks that "fa" is at least as spec-accessible
                    // as "accessibilityContext" is Java-accessible.
                    // This is vaccuously true if "accessibilityLowerBound" is private.
                    if (accessibilityLowerBound != ACC_LOW_BOUND_Private) {
                        boolean isAccessibleEnough;
                        if (Modifiers.isPublic(fa.decl.modifiers) ||
                            GetSpec.findModifierPragma(fa.decl,
                                                       TagConstants.SPEC_PUBLIC) != null) {
                            // public and spec_public fields are always accessible
                            isAccessibleEnough = true;
	    
                        } else if (Modifiers.isPrivate(fa.decl.modifiers)) {
                            // Note:  if "fa" type-checked so far, then "fa.decl"
                            // and "accessibilityContext" are declared in the same class.
                            // It would be nice to assert this fact at run-time, but control
                            // may reach this point even if "fa" does not type-check above.

                            // "fa.decl" can be private only if "accessibilityContext" is
                            // private, which was checked above
                            isAccessibleEnough = false;
	    
                        } else if (Modifiers.isPackage(fa.decl.modifiers)) {
                            // Note:  if "fa" type-checked so far, then "fa.decl" and
                            // "accessibilityContext" are declared in the same package.
                            // It would be nice to assert this fact at run-time, but control
                            // may reach this point even if "fa" does not type-check above.

                            // "fa.decl" can be package (default) accessible only if
                            // "accessibilityContext" is private (which was checked above)
                            // or package
                            isAccessibleEnough =
                                (accessibilityLowerBound == ACC_LOW_BOUND_Package);
	    
                        } else {
                            Assert.notFalse(Modifiers.isProtected(fa.decl.modifiers));
                            // Note:  if "fa" type-checked so far, then either "fa.decl" and
                            // "accessibilityContext" are declared in the same package or
                            // the class declaring "accessibilityContext" is a subtype of
                            // the class declaring "fa.decl".
                            // It would be nice to assert this fact at run-time, but control
                            // may reach this point even if "fa" does not type-check above.

                            // "fa.decl" can be protected only if "accessibilityContext" is
                            // private (which was checked above) or package, or if
                            // "accessibilityContext" is protected and "fa.decl" is
                            // declared in a superclass of the class that declares
                            // "accessibilityContext".
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
            case TagConstants.DOTDOT:
                {
                    BinaryExpr be = (BinaryExpr)e;
                    // each argument is allowed to contain quantifiers and labels
                    // if this expression is
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

            case TagConstants.SUBTYPE:
                {
                    BinaryExpr be = (BinaryExpr)e;
                    Type expected = (tag == TagConstants.SUBTYPE ?
                                     Types.typecodeType : Types.booleanType);
                    be.left = checkExpr(env, be.left, expected);
                    be.right = checkExpr(env, be.right, expected);
                    setType(e, Types.booleanType);
                    return e;
                }

            case TagConstants.FRESH:
                {
                    NaryExpr ne = (NaryExpr)e;
                    if( ne.exprs.size() != 1 ) {
                        ErrorSet.error( ne.sloc, 
                                        "The function fresh takes only one argument");
                    } else if (!isTwoStateContext) {
                        ErrorSet.error(ne.sloc, "The function \\fresh cannot be used in this context");
                    } else if (isInsidePRE) {
                        ErrorSet.error(ne.sloc, "The function \\fresh cannot be used "+
                                       "inside a \\old expression");
                    } else {
                        Expr nu = 
                            checkExpr(env, ne.exprs.elementAt(0), Types.javaLangObject());
                        ne.exprs.setElementAt( nu, 0 );			
                    }
                    setType( e, Types.booleanType);
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
                        // the first argument should be a TypeExpr; retrieve the type it
                        // denotes
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

            case TagConstants.ELEMTYPE:
                {
                    NaryExpr ne = (NaryExpr)e;
                    if( ne.exprs.size() != 1 ) 
                        ErrorSet.error( ne.sloc, 
                                        "The function \\elemtype takes only one argument");
                    else {
                        Expr nu = checkExpr(env, ne.exprs.elementAt(0), Types.typecodeType);
                        ne.exprs.setElementAt( nu, 0 );			
                    }
                    setType( e, Types.typecodeType );
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

            case TagConstants.FORALL:
            case TagConstants.EXISTS:
                {
                    QuantifiedExpr qe = (QuantifiedExpr)e;
	
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
                    setType(e, Types.booleanType);
                    return e;
                }

            case TagConstants.PARENEXPR:
            case TagConstants.NOT:
                {
                    // the sub-expression is allowed to contain quantifiers and labels
                    // if this expression is
                    isPredicateContext = isCurrentlyPredicateContext;
                    return super.checkExpr(env, e);
                }

            case TagConstants.OR:
            case TagConstants.AND:
            case TagConstants.EQ:
            case TagConstants.NE:
                {
                    BinaryExpr be = (BinaryExpr)e;
                    // each argument is allowed to contain quantifiers and labels
                    // if this expression is
                    isPredicateContext = isCurrentlyPredicateContext;
                    be.left = checkExpr(env, be.left);
                    isPredicateContext = isCurrentlyPredicateContext;
                    be.right = checkExpr(env, be.right);
                    Type t = checkBinaryExpr(be.op, be.left, be.right, be.locOp);
                    setType( be, t );
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
                            setType( r, Types.intType );
                            ErrorSet.error( r.locOpenBracket, 
                                            "Attempt to index an non-array value");
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
                        setType( r, Types.intType );
                        ErrorSet.error( r.locOpenBracket, 
                                        "Attempt to index an non-array value");
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

	    case TagConstants.EVERYTHINGEXPR:
		{
		    if (!isCurrentlySpecDesignatorContext) {
			ErrorSet.error(e.getStartLoc(),
				"Keyword \\everything is not allowed in this context");
		    } 
		    setType( e, Types.voidType);
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
                    if (inAnnotation) {
                        ErrorSet.error(e.getStartLoc(),
                                       "new cannot be used in specification expressions");
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
                    if (inAnnotation) {
                        BinaryExpr be = (BinaryExpr)e;
                        ErrorSet.error(be.locOp,
                                       "assignments cannot be used in specification expressions");
                    }
                    return super.checkExpr(env, e);
                }
      
            case TagConstants.INC: case TagConstants.DEC: 
            case TagConstants.POSTFIXINC: case TagConstants.POSTFIXDEC:
                {
                    if (inAnnotation) {
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
        inAnnotation = true;	// Must be reset before we exit!
        int tag = e.getTag();

        switch(tag) {
            case TagConstants.AXIOM:
            case TagConstants.INVARIANT:
	    case TagConstants.JML_CONSTRAINT: // FIXME - do we need to change the logic below to handle constraints?
	    case TagConstants.JML_REPRESENTS:
                {
                    ExprDeclPragma ep = (ExprDeclPragma)e;
                    Env rootEnv = (tag == TagConstants.AXIOM) ? rootSEnv : rootIEnv;

                    invariantContext = (tag == TagConstants.INVARIANT);
                    boolean oldIsLocksetContext = isLocksetContext;
                    isLocksetContext = false;
                    if (invariantContext){
                        Assert.notFalse(countFreeVarsAccesses == 0);
                        countFreeVarsAccesses = 0;
                    }
	
                    ep.expr = checkPredicate(rootEnv, ep.expr);
                    isLocksetContext = oldIsLocksetContext;

                    TypeSig sig = TypeSig.getSig(e.getParent());
                    if (sig==javafe.tc.Types.javaLangObject() ||
                        sig==javafe.tc.Types.javaLangCloneable()) {
                        ErrorSet.fatal(e.getStartLoc(),
                                       "java.lang.Object and java.lang.Cloneable may not"
                                       + " contain invariants.");
                    }
                    if (invariantContext && countFreeVarsAccesses == 0){
                        ErrorSet.error(e.getStartLoc(),
                                       "Class invariants must mention program variables"
                                       + " or fields.");
                    }

                    if (invariantContext) {countFreeVarsAccesses = 0;}
                    invariantContext = false;
                    break;
                }

	    case TagConstants.JML_DEPENDS:
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

	    case TagConstants.MODELMETHODDECLPRAGMA: {
                MethodDecl decl = ((ModelMethodDeclPragma)e).decl;
                Env rootEnv = Modifiers.isStatic(decl.modifiers)
                    ? rootSEnv
                    : rootIEnv;
		// FIXME -- need to do some checks???
		break;
            }

	    case TagConstants.MODELDECLPRAGMA: {
                FieldDecl decl = ((ModelDeclPragma)e).decl;
                Env rootEnv = Modifiers.isStatic(decl.modifiers)
                    ? rootSEnv
                    : rootIEnv;

                checkModifierPragmaVec( decl.pmodifiers, decl, rootEnv );


                /*
                 * Check for other fields with the same name:
                 */
                if (sig.hasField(decl.id) ||
                    (((GhostEnv)rootEnv).getGhostField(decl.id.toString(), decl)
                     !=null)) {
                    ErrorSet.error(decl.locId,
                                   "Another field named '"+decl.id.toString()
                                   +"' already exists in this type");
                }
// FIXME - CHeck for other model fields

                /*
                 * All that remains to be done is to prep the Type:
                 */
                rootEnv.resolveType( decl.type );

                break;
            }

            case TagConstants.GHOSTDECLPRAGMA: {
                FieldDecl decl = ((GhostDeclPragma)e).decl;
                Env rootEnv = Modifiers.isStatic(decl.modifiers)
                    ? rootSEnv
                    : rootIEnv;

                /*
                 * Check modifiers:
                 */
/* This is not the case ???
                if (!Modifiers.isPublic(decl.modifiers)) {
                    ErrorSet.error(decl.locId,
                                   "Ghost fields must be declared public");
                }
                if ((decl.modifiers
                     & ~(Modifiers.ACCESS_MODIFIERS|Modifiers.ACC_STATIC)) != 0) {
                    ErrorSet.error(decl.locId,
                                   "Ghost-field modifiers may only be public or static");
                }
*/

                checkModifierPragmaVec( decl.pmodifiers, decl, rootEnv );


                /*
                 * Handle initializer:
                 */
                if (decl.init != null) {
                    ErrorSet.error(decl.init.getStartLoc(),
                                   "Ghost fields may not have initializers");
                }

                /*
                 * Check for other fields with the same name:
                 */
                if (sig.hasField(decl.id) ||
                    (((GhostEnv)rootEnv).getGhostField(decl.id.toString(), decl)
                     !=null)) {
                    ErrorSet.error(decl.locId,
                                   "Another field named '"+decl.id.toString()
                                   +"' already exists in this type");
                }

                /*
                 * All that remains to be done is to prep the Type:
                 */
                rootEnv.resolveType( decl.type );

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
        inAnnotation = false;
    }

    protected void checkModifierPragma(ModifierPragma p, ASTNode ctxt, Env env) {

        inAnnotation = true;	// Must be reset before we exit!
        int tag = p.getTag();
        switch(tag) 
        {
	    case TagConstants.JML_EVERYTHING:
	    case TagConstants.EVERYTHINGEXPR:
	    case TagConstants.JML_NOTHING:
	    case TagConstants.NOTHINGEXPR:
	    case TagConstants.JML_NOT_SPECIFIED:
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
                        if (getOverrideStatus(md) != MSTATUS_NEW_ROUTINE) {
                            ErrorSet.error(md.getStartLoc(),
                                           "'non_null' cannot be used on method overrides; "+
                                           "use 'also_ensures \\result != null;' instead");
                        } else if (!Types.isReferenceType(md.returnType)) {
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
      
            case TagConstants.SPEC_PUBLIC:
                {
                    if( ctxt.getTag() != TagConstants.FIELDDECL ) {
                        int loc;
                        if (ctxt instanceof GenericVarDecl)
                            loc = ((GenericVarDecl)ctxt).locId;
                        else
                            loc = p.getStartLoc();
                        ErrorSet.error(loc,
                                       "The spec_public annotation can occur only on "
                                       +"field declarations");
                    } else {
                        FieldDecl fd = (FieldDecl)ctxt;
                        if (Modifiers.isPublic(fd.modifiers)) {
                            ErrorSet.error(fd.locId,
                                           "The spec_public annotation can occur only on "
                                           +"non-public field declarations");
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

	    case TagConstants.JML_PURE:
		{
		    if (ctxt instanceof ConstructorDecl) {
			((ConstructorDecl)ctxt).modifiers |= Modifiers.ACC_PURE;
		    } else if (ctxt instanceof MethodDecl) {
			((MethodDecl)ctxt).modifiers |= Modifiers.ACC_PURE;
		    } else {
			ErrorSet.error(p.getStartLoc(),
				"Expected pure to modify a constructor or method declaration");
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

            case TagConstants.ALSO_REQUIRES:
            case TagConstants.REQUIRES:
            case TagConstants.JML_PRE:
                {
                    ExprModifierPragma emp = (ExprModifierPragma)p;

                    if( !(ctxt instanceof RoutineDecl ) ) {
                        ErrorSet.error(p.getStartLoc(), TagConstants.toString(tag) +
                                       " annotations can occur only on method" +
                                       ((tag == TagConstants.REQUIRES || 
                                         tag == TagConstants.JML_PRE) ? " and constructor" : "") +
                                       " declarations");
                    } else {
                        RoutineDecl rd = (RoutineDecl)ctxt;

                        int ms = getOverrideStatus(rd);
                        if (ms == MSTATUS_NEW_ROUTINE) {
                            if (tag == TagConstants.ALSO_REQUIRES) {
                                ErrorSet.error(p.getStartLoc(), TagConstants.toString(tag) +
                                               " can only be used on method overrides; use " +
                                               TagConstants.toString(TagConstants.REQUIRES) +
                                               " instead");
                            }
                        } else if (ms == MSTATUS_CLASS_NEW_METHOD) {
                            if (tag == TagConstants.REQUIRES || tag == TagConstants.JML_PRE) {
                                String remedy;
                                if (Main.allowAlsoRequires) {
                                    remedy = "declare in supertype or use " +
                                        TagConstants.toString(TagConstants.ALSO_REQUIRES);
                                } else {
                                    remedy = "try declaring in supertype instead";
                                }
                                ErrorSet.error(p.getStartLoc(), TagConstants.toString(tag) +
                                               " cannot be used on method overrides; " +
                                               remedy);
                            }
                        } else {
                            Assert.notFalse(ms == MSTATUS_OVERRIDE);
                            if (tag == TagConstants.REQUIRES || tag == TagConstants.JML_PRE) {
                                ErrorSet.error(p.getStartLoc(), TagConstants.toString(tag) +
                                               " cannot be used on method overrides");
                            } else {
                                ErrorSet.error(p.getStartLoc(), TagConstants.toString(tag) + 
                                               " can only be used on class-new method overrides");
                            }
                        }

                        if (rd instanceof ConstructorDecl) {
                            env = env.asStaticContext();
                        }
                        int oldAccessibilityLowerBound = accessibilityLowerBound;
                        ASTNode oldAccessibilityContext = accessibilityContext;
                        accessibilityLowerBound = getAccessibility(rd.modifiers);
                        accessibilityContext = rd;
                        emp.expr = checkPredicate(env, emp.expr);
                        accessibilityLowerBound = oldAccessibilityLowerBound;
                        accessibilityContext = oldAccessibilityContext;
                    }
                    break;
                }

	    case TagConstants.JML_DIVERGES:
	    case TagConstants.JML_DIVERGES_REDUNDANTLY:
            case TagConstants.ENSURES:
            case TagConstants.ALSO_ENSURES:
            case TagConstants.JML_POST:
	    case TagConstants.JML_WHEN:
	    case TagConstants.JML_WHEN_REDUNDANTLY:
                {
                    ExprModifierPragma emp = (ExprModifierPragma)p;

                    if( !(ctxt instanceof RoutineDecl ) ) {
                        ErrorSet.error(p.getStartLoc(),
                                       TagConstants.toString(tag)
                                       +" annotations can occur only on "
                                       +"method and constructor declarations");
                    } else {
                        RoutineDecl rd = (RoutineDecl)ctxt;
/*
                        if (getOverrideStatus(rd) != MSTATUS_NEW_ROUTINE) {
                            if (tag == TagConstants.ENSURES) {
                                ErrorSet.error(p.getStartLoc(),
                                               "ensures cannot be used on method overrides; "+
                                               "use also_ensures instead");
                            }
                        } else {
                            if (tag == TagConstants.ALSO_ENSURES) {
                                ErrorSet.error(p.getStartLoc(),
                                               "also_ensures can be used only on method " +
                                               "overrides; use ensures instead");
                            }
                        }
*/
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
                        emp.expr = checkPredicate(env, emp.expr);
                        isRESContext = oldIsRESContext;
                        isTwoStateContext = oldIsTwoStateContext;
                        isPrivateFieldAccessAllowed = oldIsPrivFieldAccessAllowed;
                    }
                    break;
                }


            case TagConstants.EXSURES:
            case TagConstants.ALSO_EXSURES:
            case TagConstants.JML_SIGNALS:
                {
                    VarExprModifierPragma vemp = (VarExprModifierPragma)p;

                    if( !(ctxt instanceof RoutineDecl ) ) {
                        ErrorSet.error(p.getStartLoc(),
                                       TagConstants.toString(tag)
                                       +" annotations can occur only on "
                                       +"method and constructor declarations");
                    } else {
                        RoutineDecl rd = (RoutineDecl)ctxt;

                        // Check for correct use of exsures vs. also_exsures
                        if (getOverrideStatus(rd) != MSTATUS_NEW_ROUTINE) {
                            if (tag == TagConstants.EXSURES ||
                                tag == TagConstants.JML_SIGNALS) {
                                ErrorSet.error(p.getStartLoc(),
                                               "exsures cannot be used on method overrides; "+
                                               "use also_exsures instead");
                            }
                        } else {
                            if (tag == TagConstants.ALSO_EXSURES) {
                                ErrorSet.error(p.getStartLoc(),
                                               "also_exsures can be used only on method " +
                                               "overrides; use exsures instead");
                            }
                        }

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
                                ErrorSet.error(vemp.arg.type.getStartLoc(),
                                               "The type of the " +
                                               TagConstants.toString(tag) +
                                               " argument must be comparable to some type " +
                                               "mentioned in the routine's throws set");
                            }
                        }

                        Env subenv = new EnvForLocals(env, vemp.arg);
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
                        vemp.expr = checkPredicate(subenv, vemp.expr);
                        isTwoStateContext = oldIsTwoStateContext;
                        isPrivateFieldAccessAllowed = oldIsPrivFieldAccessAllowed;
                    }
                    break;
                }

            case TagConstants.MONITORED_BY:
                {
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
            case TagConstants.ALSO_MODIFIES:
            case TagConstants.JML_MODIFIABLE:
            case TagConstants.JML_ASSIGNABLE:
	    case TagConstants.JML_MEASURED_BY:
                {
                    CondExprModifierPragma emp = (CondExprModifierPragma)p;

                    if (!(ctxt instanceof RoutineDecl ) ) {
                        ErrorSet.error(p.getStartLoc(),
                                       "A modifies/also_modifies annotation " +
                                       "can occur only on " +
                                       "method and constructor declarations");
                    } else {
                        RoutineDecl rd = (RoutineDecl)ctxt;
	    
/*
                        if (getOverrideStatus(rd) != MSTATUS_NEW_ROUTINE) {
                            if (tag == TagConstants.MODIFIES
                                || tag == TagConstants.JML_MODIFIABLE
                                || tag == TagConstants.JML_ASSIGNABLE) {
                                ErrorSet.error(p.getStartLoc(),
				   "modifies cannot be used on method " +
				   "overrides; use also_modifies instead");
                            }
                        } else {
                            if (tag == TagConstants.ALSO_MODIFIES) {
                                ErrorSet.error(p.getStartLoc(),
				   "also_modifies can be used only on method " +
				   "overrides; use modifies instead");
                            }
                        }
*/
                        Assert.notFalse(!isSpecDesignatorContext);
                        isSpecDesignatorContext = true;
                        if (rd instanceof ConstructorDecl) {
                            // disallow "this" from constructor "modifies" clauses
                            env = env.asStaticContext();
                        }
                        emp.expr = checkDesignator(env, emp.expr);
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
                                ErrorSet.error(emp.expr.getStartLoc(),
                                               "Not a specification designator expression");
                        }
                        isSpecDesignatorContext = false;
			if (emp.cond != null) emp.cond = checkExpr(env, emp.cond);
                    }
                    break;
                }

	    case TagConstants.JML_OPENPRAGMA:
	    case TagConstants.JML_CLOSEPRAGMA:
	    case TagConstants.JML_ALSO:
	    case TagConstants.JML_NORMAL_BEHAVIOR:
	    case TagConstants.JML_EXCEPTIONAL_BEHAVIOR:
	    case TagConstants.JML_BEHAVIOR:
		// Make these unexpected again after the desugaring is implemented
		break;

            default:
                Assert.fail("Unexpected tag " + tag);
        }
        inAnnotation = false;
    }

    /**
     * Returns whether or not <code>md</code> can be overridden in some
     * possible subclass.
     */

    public static boolean isOverridable(/*@ non_null */ MethodDecl md) {
        return !(Modifiers.isPrivate(md.modifiers) ||
                 Modifiers.isFinal(md.modifiers) ||
                 Modifiers.isFinal(md.parent.modifiers) ||
                 Modifiers.isStatic(md.modifiers));
    }

    /**
     * Returns a value appropriate for assignment to
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

    protected void checkStmtPragma(Env e, StmtPragma s) {
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

                if (set.target instanceof FieldAccess) {
                    FieldAccess fa = (FieldAccess)set.target;
                    if (fa.decl == null || !GhostEnv.isGhostField(fa.decl))
                        ErrorSet.error(fa.locId,
                                       "Can use set only on ghost fields");
		
                } else
                    ErrorSet.error(set.getStartLoc(),
                                   "Can use set only on fields");

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
            case TagConstants.JML_MAINTAINING:
                {
                    ExprStmtPragma lis = (ExprStmtPragma)s;
                    loopInvariants.addElement(lis);
                    break;
                }

            case TagConstants.DECREASES:
            case TagConstants.JML_DECREASING:
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
                Assert.fail("Unexpected tag " + tag +" "+s);
        }
        inAnnotation = false;
    }


    // Utility routines

    /**
     * Copy the Type associated with an expression by the typechecking
     * pass to another Expr.  This is used by Substitute to ensure it
     * returns an Expr of the same Type.
     */
    public static void copyType(VarInit from, VarInit to) {
	Type t = getTypeOrNull(from);
	if (t != null)
	    setType(to, t);
    }


    /**
     * Return a set of *all* the methods a given method overrides. <p>
     *
     * This includes transitivity.<p>
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


    /**
     * If <code>md</code> is a method that overrides a method in a
     * superclass, the overridden method is returned.  Otherwise, if
     * <code>md</code> overrides a method in an interface, such a
     * method is returned.  Otherwise, <code>null</code> is returned.
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
                    // declared in Object, because every interface has the methods
                    // of Object.  In this case, pick the method override that
                    // does not reside in Object.
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
     * Returns whether or not <code>rd</code> is a method override
     * declaration, that is, whether or not <code>rd</code> overrides
     * a method declared in a superclass or superinterface.
     */

    public static boolean isMethodOverride(RoutineDecl rd) {
        return getOverrideStatus(rd) != MSTATUS_NEW_ROUTINE;
    }	

    static public final int MSTATUS_NEW_ROUTINE = 0;
    static public final int MSTATUS_CLASS_NEW_METHOD = 1;
    static public final int MSTATUS_OVERRIDE = 2;

    /**
     * Returns <code>MSTATUS_NEW_ROUTINE</code> if <code>rd</code> is
     * a routine that doesn't override any other method.  This
     * includes the case where <code>rd</code> is a constructor or a
     * static method.
     *
     * Returns <code>MSTATUS_CLASS_NEW_METHOD</code> if
     * <code>rd</code> is a method declared in a class, doesn't
     * override any method in any superclass, but overrides a method
     * in an interface.
     *
     * Otherwise, returns <code>MSTATUS_OVERRIDE</code>.
     */

    /*@ ensures \result == MSTATUS_NEW_ROUTINE ||
     \result == MSTATUS_CLASS_NEW_METHOD ||
     \result == MSTATUS_OVERRIDE; */
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

    protected Expr checkDesignator(Env env, Expr e) {
	if (e instanceof AmbiguousVariableAccess) 
		return super.checkDesignator(env,e);

	return e;
    }

}
